use crate::{F, PUBLIC_INPUT_START, ZERO_VEC_PTR, ir::*, lang::*};
use lean_vm::*;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use std::collections::BTreeMap;
use utils::ToUsize;

impl IntermediateInstruction {
    const fn is_hint(&self) -> bool {
        match self {
            Self::RequestMemory { .. }
            | Self::Print { .. }
            | Self::DecomposeBits { .. }
            | Self::CounterHint { .. }
            | Self::Inverse { .. }
            | Self::LocationReport { .. } => true,
            Self::Computation { .. }
            | Self::Panic
            | Self::Deref { .. }
            | Self::JumpIfNotZero { .. }
            | Self::Jump { .. }
            | Self::Poseidon2_16 { .. }
            | Self::Poseidon2_24 { .. }
            | Self::DotProduct { .. }
            | Self::MultilinearEval { .. } => false,
        }
    }
}

struct Compiler {
    memory_size_per_function: BTreeMap<String, usize>,
    label_to_pc: BTreeMap<Label, CodeAddress>,
    match_block_sizes: Vec<usize>,
    match_first_block_starts: Vec<CodeAddress>,
}

pub fn compile_to_low_level_bytecode(
    mut intermediate_bytecode: IntermediateBytecode,
) -> Result<Bytecode, String> {
    intermediate_bytecode.bytecode.insert(
        Label::EndProgram,
        vec![IntermediateInstruction::Jump {
            dest: IntermediateValue::label(Label::EndProgram),
            updated_fp: None,
        }],
    );

    let starting_frame_memory = *intermediate_bytecode
        .memory_size_per_function
        .get("main")
        .unwrap();

    let mut label_to_pc = BTreeMap::new();
    label_to_pc.insert(Label::function("main"), 0);
    let entrypoint = intermediate_bytecode
        .bytecode
        .remove(&Label::function("main"))
        .ok_or("No main function found in the compiled program")?;

    let mut code_blocks = vec![(0, entrypoint.clone())];
    let mut pc = count_real_instructions(&entrypoint);
    for (label, instructions) in &intermediate_bytecode.bytecode {
        label_to_pc.insert(label.clone(), pc);
        code_blocks.push((pc, instructions.clone()));
        pc += count_real_instructions(instructions);
    }

    let ending_pc = label_to_pc.get(&Label::EndProgram).copied().unwrap();

    let mut match_block_sizes = Vec::new();
    let mut match_first_block_starts = Vec::new();
    for match_statement in intermediate_bytecode.match_blocks {
        let max_block_size = match_statement
            .iter()
            .map(|block| count_real_instructions(block))
            .max()
            .unwrap();
        match_first_block_starts.push(pc);
        match_block_sizes.push(max_block_size);

        for mut block in match_statement {
            // fill the end of block with unreachable instructions
            block.extend(vec![
                IntermediateInstruction::Panic;
                max_block_size - count_real_instructions(&block)
            ]);
            code_blocks.push((pc, block));
            pc += max_block_size;
        }
    }

    let mut low_level_bytecode = Vec::new();
    let mut hints = BTreeMap::new();

    for (label, pc) in label_to_pc.clone() {
        hints
            .entry(pc)
            .or_insert_with(Vec::new)
            .push(Hint::Label { label });
    }

    let compiler = Compiler {
        memory_size_per_function: intermediate_bytecode.memory_size_per_function,
        label_to_pc,
        match_block_sizes,
        match_first_block_starts,
    };

    for (pc_start, block) in code_blocks {
        compile_block(
            &compiler,
            &block,
            pc_start,
            &mut low_level_bytecode,
            &mut hints,
        );
    }

    Ok(Bytecode {
        instructions: low_level_bytecode,
        hints,
        starting_frame_memory,
        ending_pc,
    })
}

fn compile_block(
    compiler: &Compiler,
    block: &[IntermediateInstruction],
    pc_start: CodeAddress,
    low_level_bytecode: &mut Vec<Instruction>,
    hints: &mut BTreeMap<CodeAddress, Vec<Hint>>,
) {
    let try_as_mem_or_constant = |value: &IntermediateValue| {
        if let Some(cst) = try_as_constant(value, compiler) {
            return Some(MemOrConstant::Constant(cst));
        }
        if let IntermediateValue::MemoryAfterFp { offset } = value {
            return Some(MemOrConstant::MemoryAfterFp {
                offset: eval_const_expression_usize(offset, compiler),
            });
        }
        None
    };

    let try_as_mem_or_fp = |value: &IntermediateValue| match value {
        IntermediateValue::MemoryAfterFp { offset } => Some(MemOrFp::MemoryAfterFp {
            offset: eval_const_expression_usize(offset, compiler),
        }),
        IntermediateValue::Fp => Some(MemOrFp::Fp),
        _ => None,
    };

    let codegen_jump = |hints: &BTreeMap<CodeAddress, Vec<Hint>>,
                        low_level_bytecode: &mut Vec<Instruction>,
                        condition: IntermediateValue,
                        dest: IntermediateValue,
                        updated_fp: Option<IntermediateValue>| {
        let dest =
            try_as_mem_or_constant(&dest).expect("Fatal: Could not materialize jump destination");
        let label = match dest {
            MemOrConstant::Constant(dest) => hints
                .get(&usize::try_from(dest.as_canonical_u32()).unwrap())
                .and_then(|hints: &Vec<Hint>| {
                    hints.iter().find_map(|x| match x {
                        Hint::Label { label } => Some(label),
                        _ => None,
                    })
                })
                .expect("Fatal: Unlabeled jump destination")
                .clone(),
            MemOrConstant::MemoryAfterFp { offset } => Label::custom(format!("fp+{offset}")),
        };
        let updated_fp = updated_fp
            .map(|fp| try_as_mem_or_fp(&fp).unwrap())
            .unwrap_or(MemOrFp::Fp);
        low_level_bytecode.push(Instruction::Jump {
            condition: try_as_mem_or_constant(&condition).unwrap(),
            label,
            dest,
            updated_fp,
        });
    };

    let mut pc = pc_start;
    for instruction in block {
        match instruction.clone() {
            IntermediateInstruction::Computation {
                operation,
                mut arg_a,
                mut arg_c,
                res,
            } => {
                if let Some(arg_a_cst) = try_as_constant(&arg_a, compiler)
                    && let Some(arg_b_cst) = try_as_constant(&arg_c, compiler)
                {
                    // res = constant +/x constant

                    let op_res = operation.compute(arg_a_cst, arg_b_cst);

                    let res: MemOrFp = res.try_into_mem_or_fp(compiler).unwrap();

                    low_level_bytecode.push(Instruction::Computation {
                        operation: Operation::Add,
                        arg_a: MemOrConstant::zero(),
                        arg_c: res,
                        res: MemOrConstant::Constant(op_res),
                    });
                    pc += 1;
                    continue;
                }

                if arg_c.is_constant() {
                    std::mem::swap(&mut arg_a, &mut arg_c);
                }

                low_level_bytecode.push(Instruction::Computation {
                    operation,
                    arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                    arg_c: try_as_mem_or_fp(&arg_c).unwrap(),
                    res: try_as_mem_or_constant(&res).unwrap(),
                });
            }
            IntermediateInstruction::Panic => {
                low_level_bytecode.push(Instruction::Computation {
                    // fp x 0 = 1 is impossible, so we can use it to panic
                    operation: Operation::Mul,
                    arg_a: MemOrConstant::zero(),
                    arg_c: MemOrFp::Fp,
                    res: MemOrConstant::one(),
                });
            }
            IntermediateInstruction::Deref {
                shift_0,
                shift_1,
                res,
            } => {
                low_level_bytecode.push(Instruction::Deref {
                    shift_0: eval_const_expression(&shift_0, compiler).to_usize(),
                    shift_1: eval_const_expression(&shift_1, compiler).to_usize(),
                    res: match res {
                        IntermediaryMemOrFpOrConstant::MemoryAfterFp { offset } => {
                            MemOrFpOrConstant::MemoryAfterFp {
                                offset: eval_const_expression_usize(&offset, compiler),
                            }
                        }
                        IntermediaryMemOrFpOrConstant::Fp => MemOrFpOrConstant::Fp,
                        IntermediaryMemOrFpOrConstant::Constant(c) => {
                            MemOrFpOrConstant::Constant(eval_const_expression(&c, compiler))
                        }
                    },
                });
            }
            IntermediateInstruction::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => codegen_jump(hints, low_level_bytecode, condition, dest, updated_fp),
            IntermediateInstruction::Jump { dest, updated_fp } => {
                let one =
                    IntermediateValue::Constant(ConstExpression::Value(ConstantValue::Scalar(1)));
                codegen_jump(hints, low_level_bytecode, one, dest, updated_fp)
            }
            IntermediateInstruction::Poseidon2_16 { arg_a, arg_b, res } => {
                low_level_bytecode.push(Instruction::Poseidon2_16 {
                    arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                    arg_b: try_as_mem_or_constant(&arg_b).unwrap(),
                    res: try_as_mem_or_fp(&res).unwrap(),
                });
            }
            IntermediateInstruction::Poseidon2_24 { arg_a, arg_b, res } => {
                low_level_bytecode.push(Instruction::Poseidon2_24 {
                    arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                    arg_b: try_as_mem_or_constant(&arg_b).unwrap(),
                    res: try_as_mem_or_fp(&res).unwrap(),
                });
            }
            IntermediateInstruction::DotProduct {
                arg0,
                arg1,
                res,
                size,
            } => {
                low_level_bytecode.push(Instruction::DotProductExtensionExtension {
                    arg0: arg0.try_into_mem_or_constant(compiler).unwrap(),
                    arg1: arg1.try_into_mem_or_constant(compiler).unwrap(),
                    res: res.try_into_mem_or_fp(compiler).unwrap(),
                    size: eval_const_expression_usize(&size, compiler),
                });
            }
            IntermediateInstruction::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                low_level_bytecode.push(Instruction::MultilinearEval {
                    coeffs: coeffs.try_into_mem_or_constant(compiler).unwrap(),
                    point: point.try_into_mem_or_constant(compiler).unwrap(),
                    res: res.try_into_mem_or_fp(compiler).unwrap(),
                    n_vars: eval_const_expression_usize(&n_vars, compiler),
                });
            }
            IntermediateInstruction::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                let hint = Hint::DecomposeBits {
                    res_offset,
                    to_decompose: to_decompose
                        .iter()
                        .map(|expr| try_as_mem_or_constant(expr).unwrap())
                        .collect(),
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::CounterHint { res_offset } => {
                let hint = Hint::CounterHint { res_offset };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::Inverse { arg, res_offset } => {
                let hint = Hint::Inverse {
                    arg: try_as_mem_or_constant(&arg).unwrap(),
                    res_offset,
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::RequestMemory {
                offset,
                size,
                vectorized,
                vectorized_len,
            } => {
                let size = try_as_mem_or_constant(&size).unwrap();
                let vectorized_len = try_as_constant(&vectorized_len, compiler)
                    .unwrap()
                    .to_usize();
                let hint = Hint::RequestMemory {
                    offset: eval_const_expression_usize(&offset, compiler),
                    vectorized,
                    size,
                    vectorized_len,
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::Print { line_info, content } => {
                let hint = Hint::Print {
                    line_info: line_info.clone(),
                    content: content
                        .into_iter()
                        .map(|c| try_as_mem_or_constant(&c).unwrap())
                        .collect(),
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::LocationReport { location } => {
                let hint = Hint::LocationReport { location };
                hints.entry(pc).or_default().push(hint);
            }
        }

        if !instruction.is_hint() {
            pc += 1;
        }
    }
}

fn count_real_instructions(instrs: &[IntermediateInstruction]) -> usize {
    instrs.iter().filter(|instr| !instr.is_hint()).count()
}

fn eval_constant_value(constant: &ConstantValue, compiler: &Compiler) -> usize {
    match constant {
        ConstantValue::Scalar(scalar) => *scalar,
        ConstantValue::PublicInputStart => PUBLIC_INPUT_START,
        ConstantValue::PointerToZeroVector => ZERO_VEC_PTR,
        ConstantValue::PointerToOneVector => ONE_VEC_PTR,
        ConstantValue::FunctionSize { function_name } => {
            let func_name_str = match function_name {
                Label::Function(name) => name,
                _ => panic!("Expected function label, got: {function_name}"),
            };
            *compiler
                .memory_size_per_function
                .get(func_name_str)
                .unwrap_or_else(|| panic!("Function {func_name_str} not found in memory size map"))
        }
        ConstantValue::Label(label) => compiler.label_to_pc.get(label).copied().unwrap(),
        ConstantValue::MatchBlockSize { match_index } => compiler.match_block_sizes[*match_index],
        ConstantValue::MatchFirstBlockStart { match_index } => {
            compiler.match_first_block_starts[*match_index]
        }
    }
}

fn eval_const_expression(constant: &ConstExpression, compiler: &Compiler) -> F {
    constant
        .eval_with(&|cst| Some(F::from_usize(eval_constant_value(cst, compiler))))
        .unwrap()
}

fn eval_const_expression_usize(constant: &ConstExpression, compiler: &Compiler) -> usize {
    eval_const_expression(constant, compiler).to_usize()
}

fn try_as_constant(value: &IntermediateValue, compiler: &Compiler) -> Option<F> {
    if let IntermediateValue::Constant(c) = value {
        Some(eval_const_expression(c, compiler))
    } else {
        None
    }
}

impl IntermediateValue {
    fn try_into_mem_or_fp(&self, compiler: &Compiler) -> Result<MemOrFp, String> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(MemOrFp::MemoryAfterFp {
                offset: eval_const_expression_usize(offset, compiler),
            }),
            Self::Fp => Ok(MemOrFp::Fp),
            _ => Err(format!("Cannot convert {self:?} to MemOrFp")),
        }
    }
    fn try_into_mem_or_constant(&self, compiler: &Compiler) -> Result<MemOrConstant, String> {
        if let Some(cst) = try_as_constant(self, compiler) {
            return Ok(MemOrConstant::Constant(cst));
        }
        if let Self::MemoryAfterFp { offset } = self {
            return Ok(MemOrConstant::MemoryAfterFp {
                offset: eval_const_expression_usize(offset, compiler),
            });
        }
        Err(format!("Cannot convert {self:?} to MemOrConstant"))
    }
}
