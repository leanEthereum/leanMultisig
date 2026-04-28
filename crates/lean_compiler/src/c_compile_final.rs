use crate::{F, instruction_encoder::field_representation, ir::*, lang::*};
use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use utils::{ToUsize, poseidon_compress_slice};

impl IntermediateInstruction {
    const fn is_hint(&self) -> bool {
        match self {
            Self::RequestMemory { .. }
            | Self::Print { .. }
            | Self::CustomHint { .. }
            | Self::HintWitness { .. }
            | Self::Inverse { .. }
            | Self::LocationReport { .. }
            | Self::DebugAssert { .. }
            | Self::DerefHint { .. }
            | Self::PanicHint { .. }
            | Self::ParallelBatchStart { .. } => true,
            Self::Computation { .. }
            | Self::Panic
            | Self::Deref { .. }
            | Self::Fma { .. }
            | Self::JumpIfNotZero { .. }
            | Self::Jump { .. }
            | Self::Precompile(..) => false,
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
    function_locations: BTreeMap<SourceLocation, FunctionName>,
    source_code: BTreeMap<FileId, String>,
    filepaths: BTreeMap<FileId, String>,
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
        .ok_or("Missing main function")?;

    let mut hints = BTreeMap::new();
    let mut label_to_pc = BTreeMap::new();

    label_to_pc.insert(Label::EndProgram, ENDING_PC);
    let exit_point = intermediate_bytecode
        .bytecode
        .remove(&Label::EndProgram)
        .ok_or("No end_program label found in the compiled program")?;
    assert_eq!(count_real_instructions(&exit_point), STARTING_PC);

    label_to_pc.insert(Label::function("main"), STARTING_PC);
    let entrypoint = intermediate_bytecode
        .bytecode
        .remove(&Label::function("main"))
        .ok_or("No main function found in the compiled program")?;

    let mut pc = count_real_instructions(&exit_point) + count_real_instructions(&entrypoint);
    let mut code_blocks = vec![(ENDING_PC, exit_point), (STARTING_PC, entrypoint)];

    for (label, instructions) in &intermediate_bytecode.bytecode {
        label_to_pc.insert(label.clone(), pc);
        code_blocks.push((pc, instructions.clone()));
        pc += count_real_instructions(instructions);
    }

    let mut match_block_sizes = Vec::new();
    let mut match_first_block_starts = Vec::new();
    for MatchBlock { match_cases } in intermediate_bytecode.match_blocks {
        let max_block_size = match_cases
            .iter()
            .map(|block| count_real_instructions(block))
            .max()
            .unwrap();
        match_first_block_starts.push(pc);
        match_block_sizes.push(max_block_size);

        for mut block in match_cases {
            // fill the end of block with unreachable instructions
            block.extend(vec![
                IntermediateInstruction::Panic;
                max_block_size - count_real_instructions(&block)
            ]);
            code_blocks.push((pc, block));
            pc += max_block_size;
        }
    }

    for (label, pc) in label_to_pc.clone() {
        hints.entry(pc).or_insert_with(Vec::new).push(Hint::Label { label });
    }

    let compiler = Compiler {
        memory_size_per_function: intermediate_bytecode.memory_size_per_function,
        label_to_pc,
        match_block_sizes,
        match_first_block_starts,
    };

    let mut instructions = Vec::new();

    for (pc_start, block) in code_blocks {
        compile_block(&compiler, &block, pc_start, &mut instructions, &mut hints);
    }

    let min_bytecode_size = 1 << MIN_BYTECODE_LOG_SIZE;
    if instructions.len() < min_bytecode_size {
        let last = instructions.last().unwrap().clone();
        instructions.resize(min_bytecode_size, last);
    }

    let instructions_encoded = instructions.par_iter().map(field_representation).collect::<Vec<_>>();

    let mut instructions_multilinear = vec![];
    for instr in &instructions_encoded {
        instructions_multilinear.extend_from_slice(instr);
        let padding = N_INSTRUCTION_COLUMNS.next_power_of_two() - N_INSTRUCTION_COLUMNS;
        instructions_multilinear.extend(vec![F::ZERO; padding]);
    }
    instructions_multilinear.resize(instructions_multilinear.len().next_power_of_two(), F::ZERO);

    // Build pc_to_location mapping from LocationReport hints
    let mut pc_to_location = Vec::with_capacity(instructions.len());
    let mut current_location = SourceLocation {
        file_id: 0,
        line_number: 0,
    };
    for pc in 0..instructions.len() {
        if let Some(hints_at_pc) = hints.get(&pc) {
            for hint in hints_at_pc {
                if let Hint::LocationReport { location } = hint {
                    current_location = *location;
                }
            }
        }
        pc_to_location.push(current_location);
    }

    let instructions_multilinear_packed = pack_extension(
        &instructions_multilinear
            .par_iter()
            .map(|&pf| EF::from(pf))
            .collect::<Vec<EF>>(),
    );
    let hash = poseidon_compress_slice(&instructions_multilinear, true);

    let code: Vec<_> = instructions
        .into_iter()
        .enumerate()
        .map(|(pc, instruction)| CodeEntry {
            instruction,
            hints: hints.remove(&pc).unwrap_or_default().into_boxed_slice(),
        })
        .collect();
    assert!(hints.is_empty());

    Ok(Bytecode {
        code,
        instructions_multilinear,
        instructions_multilinear_packed,
        hash,
        starting_frame_memory,
        function_locations,
        source_code,
        filepaths,
        pc_to_location,
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

    let codegen_jump = |hints: &BTreeMap<CodeAddress, Vec<Hint>>,
                        low_level_bytecode: &mut Vec<Instruction>,
                        condition: IntermediateValue,
                        dest: IntermediateValue,
                        updated_fp: Option<IntermediateValue>| {
        let dest = try_as_mem_or_constant(&dest).expect("Fatal: Could not materialize jump destination");
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
            .map(|fp| fp.try_into_mem_or_fp_or_constant(compiler).unwrap())
            .unwrap_or(MemOrFpOrConstant::FpRelative { offset: 0 });
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
                mut arg_b,
                res,
            } => {
                if let Some(arg_a_cst) = try_as_constant(&arg_a, compiler)
                    && let Some(arg_b_cst) = try_as_constant(&arg_b, compiler)
                {
                    // res = constant +/x constant

                    let op_res = operation.compute(arg_a_cst, arg_b_cst);

                    low_level_bytecode.push(Instruction::Computation {
                        operation: Operation::Add,
                        arg_a: MemOrConstant::zero(),
                        arg_c: res.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                        res: MemOrConstant::Constant(op_res),
                    });
                    pc += 1;
                    continue;
                }

                if arg_b.is_constant() {
                    std::mem::swap(&mut arg_a, &mut arg_b);
                }

                low_level_bytecode.push(Instruction::Computation {
                    operation,
                    arg_a: try_as_mem_or_constant(&arg_a).unwrap(),
                    arg_c: arg_b.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                    res: try_as_mem_or_constant(&res).unwrap(),
                });
            }
            IntermediateInstruction::Panic => {
                low_level_bytecode.push(Instruction::Computation {
                    // fp x 0 = 1 is impossible, so we can use it to panic
                    operation: Operation::Mul,
                    arg_a: MemOrConstant::zero(),
                    arg_c: MemOrFpOrConstant::FpRelative { offset: 0 },
                    res: MemOrConstant::one(),
                });
            }
            IntermediateInstruction::Deref { shift_0, shift_1, res } => {
                low_level_bytecode.push(Instruction::Deref {
                    shift_0: eval_const_expression(&shift_0, compiler).to_usize(),
                    shift_1: eval_const_expression(&shift_1, compiler).to_usize(),
                    res: res.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                });
            }
            IntermediateInstruction::Fma {
                multiplier,
                src_a_offset,
                dst_offset,
                arg_c,
            } => {
                low_level_bytecode.push(Instruction::Fma {
                    multiplier: eval_const_expression(&multiplier, compiler),
                    offset_a: eval_const_expression_usize(&src_a_offset, compiler),
                    offset_b: eval_const_expression_usize(&dst_offset, compiler),
                    arg_c: arg_c.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                });
            }
            IntermediateInstruction::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => codegen_jump(hints, low_level_bytecode, condition, dest, updated_fp),
            IntermediateInstruction::Jump { dest, updated_fp } => {
                let one = ConstExpression::one().into();
                codegen_jump(hints, low_level_bytecode, one, dest, updated_fp)
            }
            IntermediateInstruction::Precompile(precompile) => {
                let data = precompile
                    .data
                    .map_size(|size| eval_const_expression_usize(&size, compiler));
                let args = PrecompileArgs {
                    arg_0: precompile.arg_0.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                    arg_1: precompile.arg_1.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                    res: precompile.res.try_into_mem_or_fp_or_constant(compiler).unwrap(),
                    data,
                };
                low_level_bytecode.push(Instruction::Precompile(args));
            }
            IntermediateInstruction::CustomHint(hint, args) => {
                let hint = Hint::Custom(
                    hint,
                    args.into_iter()
                        .map(|expr| expr.try_into_mem_or_fp_or_constant(compiler).unwrap())
                        .collect(),
                );
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::Inverse { arg, res_offset } => {
                let hint = Hint::Inverse {
                    arg: try_as_mem_or_constant(&arg).unwrap(),
                    res_offset,
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::RequestMemory { offset, size } => {
                let size = try_as_mem_or_constant(&size).unwrap();
                let hint = Hint::RequestMemory {
                    offset: eval_const_expression_usize(&offset, compiler),
                    size,
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::HintWitness { name, destination } => {
                let destination = destination.map(|offset| eval_const_expression_usize(&offset, compiler));
                hints
                    .entry(pc)
                    .or_default()
                    .push(Hint::HintWitness { name, destination });
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
            IntermediateInstruction::DebugAssert(boolean, line_number) => {
                let hint = Hint::DebugAssert(
                    BooleanExpr {
                        left: try_as_mem_or_constant(&boolean.left).unwrap(),
                        right: try_as_mem_or_constant(&boolean.right).unwrap(),
                        kind: boolean.kind,
                    },
                    line_number,
                );
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::DerefHint {
                offset_src,
                offset_target,
            } => {
                let hint = Hint::DerefHint {
                    offset_src: eval_const_expression_usize(&offset_src, compiler),
                    offset_target: eval_const_expression_usize(&offset_target, compiler),
                };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::PanicHint { message } => {
                let hint = Hint::Panic { message };
                hints.entry(pc).or_default().push(hint);
            }
            IntermediateInstruction::ParallelBatchStart { n_args, end_value } => {
                let end_value = try_as_mem_or_constant(&end_value).expect("parallel loop end value");
                hints
                    .entry(pc)
                    .or_default()
                    .push(Hint::ParallelBatchStart { n_args, end_value });
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
        ConstantValue::Scalar(scalar) => scalar.to_usize(),
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
        ConstantValue::MatchFirstBlockStart { match_index } => compiler.match_first_block_starts[*match_index],
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
    fn try_into_mem_or_fp_or_constant(&self, compiler: &Compiler) -> Result<MemOrFpOrConstant, String> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(MemOrFpOrConstant::MemoryAfterFp {
                offset: eval_const_expression_usize(offset, compiler),
            }),
            Self::FpRelative { offset } => Ok(MemOrFpOrConstant::FpRelative {
                offset: eval_const_expression_usize(offset, compiler),
            }),
            Self::Constant(c) => Ok(MemOrFpOrConstant::Constant(eval_const_expression(c, compiler))),
        }
    }
}
