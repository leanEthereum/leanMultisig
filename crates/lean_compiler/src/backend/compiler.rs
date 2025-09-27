use super::evaluation::*;
use crate::{ir::*, lang::*};
use lean_vm::*;
use p3_field::PrimeField32;
use std::collections::BTreeMap;
use utils::ToUsize;

/// Compiles intermediate bytecode to low-level VM bytecode.
///
/// This is the main entry point for the backend compilation phase,
/// taking intermediate representation and producing executable VM code.
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
        .ok_or("No main function found in memory size map")?;

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

    let compiler = CodeGenerator {
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

/// Compiles a block of intermediate instructions to low-level VM instructions.
fn compile_block(
    compiler: &CodeGenerator,
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

/// Counts the number of real instructions (non-hints) in a block.
fn count_real_instructions(instrs: &[IntermediateInstruction]) -> usize {
    instrs.iter().filter(|instr| !instr.is_hint()).count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IntermediateBytecode, IntermediateInstruction, IntermediateValue};
    use crate::lang::ConstExpression;
    use lean_vm::{Label, Operation};
    use std::collections::BTreeMap;

    #[test]
    fn test_count_real_instructions() {
        let instructions = vec![
            IntermediateInstruction::Computation {
                operation: Operation::Add,
                arg_a: IntermediateValue::Fp,
                arg_c: IntermediateValue::Constant(ConstExpression::scalar(1)),
                res: IntermediateValue::Fp,
            },
            IntermediateInstruction::Print {
                line_info: "test".to_string(),
                content: vec![],
            },
            IntermediateInstruction::Panic,
        ];

        // Only 2 real instructions (Computation and Panic), Print is a hint
        assert_eq!(count_real_instructions(&instructions), 2);
    }

    #[test]
    fn test_compile_to_low_level_bytecode_no_main() {
        let intermediate_bytecode = IntermediateBytecode {
            bytecode: BTreeMap::new(),
            match_blocks: Vec::new(),
            memory_size_per_function: BTreeMap::new(),
        };

        let result = compile_to_low_level_bytecode(intermediate_bytecode);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("No main function found"));
    }

    #[test]
    fn test_compile_to_low_level_bytecode_simple() {
        let mut bytecode = BTreeMap::new();
        let mut memory_sizes = BTreeMap::new();

        // Simple main function with one instruction
        bytecode.insert(
            Label::function("main"),
            vec![IntermediateInstruction::Panic],
        );
        memory_sizes.insert("main".to_string(), 10);

        let intermediate_bytecode = IntermediateBytecode {
            bytecode,
            match_blocks: Vec::new(),
            memory_size_per_function: memory_sizes,
        };

        let result = compile_to_low_level_bytecode(intermediate_bytecode);
        assert!(result.is_ok());

        let bytecode = result.unwrap();
        assert_eq!(bytecode.starting_frame_memory, 10);
        assert!(!bytecode.instructions.is_empty());
    }
}
