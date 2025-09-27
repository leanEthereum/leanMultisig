use crate::{codegen::*, ir::*, lang::*};
use lean_vm::*;
use std::collections::BTreeSet;
use utils::ToUsize;

/// Compiles a sequence of SimpleLine instructions to intermediate bytecode.
///
/// This function is the core of the instruction compiler, handling all
/// SimpleLine variants and managing control flow between them.
pub fn compile_lines(
    lines: &[SimpleLine],
    compiler: &mut Compiler,
    final_jump: Option<Label>,
    declared_vars: &mut BTreeSet<Var>,
) -> Result<Vec<IntermediateInstruction>, String> {
    let mut instructions = Vec::new();

    for (i, line) in lines.iter().enumerate() {
        match line {
            SimpleLine::Assignment {
                var,
                operation,
                arg0,
                arg1,
            } => {
                instructions.push(IntermediateInstruction::computation(
                    *operation,
                    IntermediateValue::from_simple_expr(arg0, compiler),
                    IntermediateValue::from_simple_expr(arg1, compiler),
                    IntermediateValue::from_var_or_const_malloc_access(var, compiler),
                ));

                mark_vars_as_declared(&[arg0, arg1], declared_vars);
                if let VarOrConstMallocAccess::Var(var) = var {
                    declared_vars.insert(var.clone());
                }
            }

            SimpleLine::Match { value, arms } => {
                let match_index = compiler.match_blocks.len();
                let end_label = Label::match_end(match_index);

                let value_simplified = IntermediateValue::from_simple_expr(value, compiler);

                let mut compiled_arms = vec![];
                let original_stack_size = compiler.stack_size;
                let mut new_stack_size = original_stack_size;
                for (i, arm) in arms.iter().enumerate() {
                    let mut arm_declared_vars = declared_vars.clone();
                    compiler.stack_size = original_stack_size;
                    let arm_instructions = compile_lines(
                        arm,
                        compiler,
                        Some(end_label.clone()),
                        &mut arm_declared_vars,
                    )?;
                    compiled_arms.push(arm_instructions);
                    new_stack_size = compiler.stack_size.max(new_stack_size);
                    *declared_vars = if i == 0 {
                        arm_declared_vars
                    } else {
                        declared_vars
                            .intersection(&arm_declared_vars)
                            .cloned()
                            .collect()
                    };
                }
                compiler.stack_size = new_stack_size;
                compiler.match_blocks.push(compiled_arms);

                let value_scaled_offset = IntermediateValue::MemoryAfterFp {
                    offset: compiler.stack_size.into(),
                };
                compiler.stack_size += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Mul,
                    arg_a: value_simplified,
                    arg_c: ConstExpression::Value(ConstantValue::MatchBlockSize { match_index })
                        .into(),
                    res: value_scaled_offset.clone(),
                });

                let jump_dest_offset = IntermediateValue::MemoryAfterFp {
                    offset: compiler.stack_size.into(),
                };
                compiler.stack_size += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Add,
                    arg_a: value_scaled_offset,
                    arg_c: ConstExpression::Value(ConstantValue::MatchFirstBlockStart {
                        match_index,
                    })
                    .into(),
                    res: jump_dest_offset.clone(),
                });
                instructions.push(IntermediateInstruction::Jump {
                    dest: jump_dest_offset,
                    updated_fp: None,
                });

                let remaining =
                    compile_lines(&lines[i + 1..], compiler, final_jump, declared_vars)?;
                compiler.bytecode.insert(end_label, remaining);

                return Ok(instructions);
            }

            SimpleLine::IfNotZero {
                condition,
                then_branch,
                else_branch,
            } => {
                validate_vars_declared(&[condition], declared_vars)?;

                let if_id = compiler.if_counter;
                compiler.if_counter += 1;

                let (if_label, else_label, end_label) = (
                    Label::if_label(if_id),
                    Label::else_label(if_id),
                    Label::if_else_end(if_id),
                );

                // c: condition
                let condition_simplified = IntermediateValue::from_simple_expr(condition, compiler);

                // 1/c (or 0 if c is zero)
                let condition_inverse_offset = compiler.stack_size;
                compiler.stack_size += 1;
                instructions.push(IntermediateInstruction::Inverse {
                    arg: condition_simplified.clone(),
                    res_offset: condition_inverse_offset,
                });

                // c x 1/c
                let product_offset = compiler.stack_size;
                compiler.stack_size += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Mul,
                    arg_a: condition_simplified.clone(),
                    arg_c: IntermediateValue::MemoryAfterFp {
                        offset: condition_inverse_offset.into(),
                    },
                    res: IntermediateValue::MemoryAfterFp {
                        offset: product_offset.into(),
                    },
                });

                // 1 - (c x 1/c)
                let one_minus_product_offset = compiler.stack_size;
                compiler.stack_size += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Add,
                    arg_a: IntermediateValue::MemoryAfterFp {
                        offset: one_minus_product_offset.into(),
                    },
                    arg_c: IntermediateValue::MemoryAfterFp {
                        offset: product_offset.into(),
                    },
                    res: ConstExpression::one().into(),
                });

                // c x (1 - (c x 1/c)) = 0
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Mul,
                    arg_a: IntermediateValue::MemoryAfterFp {
                        offset: one_minus_product_offset.into(),
                    },
                    arg_c: condition_simplified,
                    res: ConstExpression::zero().into(),
                });

                instructions.push(IntermediateInstruction::JumpIfNotZero {
                    condition: IntermediateValue::MemoryAfterFp {
                        offset: product_offset.into(),
                    }, // c x 1/c
                    dest: IntermediateValue::label(if_label.clone()),
                    updated_fp: None,
                });
                instructions.push(IntermediateInstruction::Jump {
                    dest: IntermediateValue::label(else_label.clone()),
                    updated_fp: None,
                });

                let original_stack = compiler.stack_size;

                let mut then_declared_vars = declared_vars.clone();
                let then_instructions = compile_lines(
                    then_branch,
                    compiler,
                    Some(end_label.clone()),
                    &mut then_declared_vars,
                )?;
                let then_stack = compiler.stack_size;

                compiler.stack_size = original_stack;
                let mut else_declared_vars = declared_vars.clone();
                let else_instructions = compile_lines(
                    else_branch,
                    compiler,
                    Some(end_label.clone()),
                    &mut else_declared_vars,
                )?;
                let else_stack = compiler.stack_size;

                compiler.stack_size = then_stack.max(else_stack);
                *declared_vars = then_declared_vars
                    .intersection(&else_declared_vars)
                    .cloned()
                    .collect();

                compiler.bytecode.insert(if_label, then_instructions);
                compiler.bytecode.insert(else_label, else_instructions);

                let remaining =
                    compile_lines(&lines[i + 1..], compiler, final_jump, declared_vars)?;
                compiler.bytecode.insert(end_label, remaining);

                return Ok(instructions);
            }

            SimpleLine::RawAccess { res, index, shift } => {
                validate_vars_declared(&[index], declared_vars)?;
                if let SimpleExpr::Var(var) = res {
                    declared_vars.insert(var.clone());
                }
                let shift_0 = match index {
                    SimpleExpr::Constant(c) => c.clone(),
                    _ => compiler.get_offset(&index.clone().try_into().unwrap()),
                };
                instructions.push(IntermediateInstruction::Deref {
                    shift_0,
                    shift_1: shift.clone(),
                    res: res.to_mem_after_fp_or_constant(compiler),
                });
            }

            SimpleLine::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                let call_id = compiler.call_counter;
                compiler.call_counter += 1;
                let return_label = Label::return_from_call(call_id);

                let new_fp_pos = compiler.stack_size;
                compiler.stack_size += 1;

                instructions.extend(setup_function_call(
                    function_name,
                    args,
                    new_fp_pos,
                    &return_label,
                    compiler,
                )?);

                validate_vars_declared(args, declared_vars)?;
                declared_vars.extend(return_data.iter().cloned());

                let after_call = {
                    let mut instructions = Vec::new();

                    // Copy return values
                    for (i, ret_var) in return_data.iter().enumerate() {
                        instructions.push(IntermediateInstruction::Deref {
                            shift_0: new_fp_pos.into(),
                            shift_1: (2 + args.len() + i).into(),
                            res: IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                                offset: compiler.get_offset(&ret_var.clone().into()),
                            },
                        });
                    }

                    instructions.extend(compile_lines(
                        &lines[i + 1..],
                        compiler,
                        final_jump,
                        declared_vars,
                    )?);

                    instructions
                };

                compiler.bytecode.insert(return_label, after_call);

                return Ok(instructions);
            }

            SimpleLine::Precompile { precompile, args } => {
                use crate::precompiles::PrecompileName;

                match &precompile.name {
                    PrecompileName::Poseidon16 => {
                        compile_poseidon(&mut instructions, args, compiler, true)?;
                    }
                    PrecompileName::Poseidon24 => {
                        compile_poseidon(&mut instructions, args, compiler, false)?;
                    }
                    PrecompileName::DotProduct => {
                        instructions.push(IntermediateInstruction::DotProduct {
                            arg0: IntermediateValue::from_simple_expr(&args[0], compiler),
                            arg1: IntermediateValue::from_simple_expr(&args[1], compiler),
                            res: IntermediateValue::from_simple_expr(&args[2], compiler),
                            size: args[3].as_constant().unwrap(),
                        });
                    }
                    PrecompileName::MultilinearEval => {
                        instructions.push(IntermediateInstruction::MultilinearEval {
                            coeffs: IntermediateValue::from_simple_expr(&args[0], compiler),
                            point: IntermediateValue::from_simple_expr(&args[1], compiler),
                            res: IntermediateValue::from_simple_expr(&args[2], compiler),
                            n_vars: args[3].as_constant().unwrap(),
                        });
                    }
                }
            }

            SimpleLine::FunctionRet { return_data } => {
                if compiler.func_name == "main" {
                    // pC -> ending_pc, fp -> 0
                    let zero_value_offset = IntermediateValue::MemoryAfterFp {
                        offset: compiler.stack_size.into(),
                    };
                    compiler.stack_size += 1;
                    instructions.push(IntermediateInstruction::Computation {
                        operation: Operation::Add,
                        arg_a: IntermediateValue::Constant(0.into()),
                        arg_c: IntermediateValue::Constant(0.into()),
                        res: zero_value_offset.clone(),
                    });
                    instructions.push(IntermediateInstruction::Jump {
                        dest: IntermediateValue::label(Label::EndProgram),
                        updated_fp: Some(zero_value_offset),
                    });
                } else {
                    compile_function_ret(&mut instructions, return_data, compiler);
                }
            }
            SimpleLine::Panic => instructions.push(IntermediateInstruction::Panic),
            SimpleLine::HintMAlloc {
                var,
                size,
                vectorized,
                vectorized_len,
            } => {
                declared_vars.insert(var.clone());
                instructions.push(IntermediateInstruction::RequestMemory {
                    offset: compiler.get_offset(&var.clone().into()),
                    size: IntermediateValue::from_simple_expr(size, compiler),
                    vectorized: *vectorized,
                    vectorized_len: IntermediateValue::from_simple_expr(vectorized_len, compiler),
                });
            }
            SimpleLine::ConstMalloc { var, size, label } => {
                let size = size.naive_eval().unwrap().to_usize(); // TODO not very good;
                handle_const_malloc(declared_vars, &mut instructions, compiler, var, size, label);
            }
            SimpleLine::DecomposeBits {
                var,
                to_decompose,
                label,
            } => {
                use p3_field::Field;

                instructions.push(IntermediateInstruction::DecomposeBits {
                    res_offset: compiler.stack_size,
                    to_decompose: to_decompose
                        .iter()
                        .map(|expr| IntermediateValue::from_simple_expr(expr, compiler))
                        .collect(),
                });

                handle_const_malloc(
                    declared_vars,
                    &mut instructions,
                    compiler,
                    var,
                    F::bits() * to_decompose.len(),
                    label,
                );
            }
            SimpleLine::CounterHint { var } => {
                declared_vars.insert(var.clone());
                instructions.push(IntermediateInstruction::CounterHint {
                    res_offset: compiler
                        .get_offset(&var.clone().into())
                        .naive_eval()
                        .unwrap()
                        .to_usize(),
                });
            }
            SimpleLine::Print { line_info, content } => {
                instructions.push(IntermediateInstruction::Print {
                    line_info: line_info.clone(),
                    content: content
                        .iter()
                        .map(|c| IntermediateValue::from_simple_expr(c, compiler))
                        .collect(),
                });
            }
            SimpleLine::LocationReport { location } => {
                instructions.push(IntermediateInstruction::LocationReport {
                    location: *location,
                });
            }
        }
    }

    if let Some(jump_label) = final_jump {
        instructions.push(IntermediateInstruction::Jump {
            dest: IntermediateValue::label(jump_label),
            updated_fp: None,
        });
    }

    Ok(instructions)
}

fn handle_const_malloc(
    declared_vars: &mut BTreeSet<Var>,
    instructions: &mut Vec<IntermediateInstruction>,
    compiler: &mut Compiler,
    var: &Var,
    size: usize,
    label: &ConstMallocLabel,
) {
    declared_vars.insert(var.clone());
    instructions.push(IntermediateInstruction::Computation {
        operation: Operation::Add,
        arg_a: IntermediateValue::Constant(compiler.stack_size.into()),
        arg_c: IntermediateValue::Fp,
        res: IntermediateValue::MemoryAfterFp {
            offset: compiler.get_offset(&var.clone().into()),
        },
    });
    compiler.const_mallocs.insert(*label, compiler.stack_size);
    compiler.stack_size += size;
}

// Helper functions
fn mark_vars_as_declared<VoC: std::borrow::Borrow<SimpleExpr>>(
    vocs: &[VoC],
    declared: &mut BTreeSet<Var>,
) {
    for voc in vocs {
        if let SimpleExpr::Var(v) = voc.borrow() {
            declared.insert(v.clone());
        }
    }
}

fn validate_vars_declared<VoC: std::borrow::Borrow<SimpleExpr>>(
    vocs: &[VoC],
    declared: &BTreeSet<Var>,
) -> Result<(), String> {
    for voc in vocs {
        if let SimpleExpr::Var(v) = voc.borrow()
            && !declared.contains(v)
        {
            return Err(format!("Variable {v} not declared"));
        }
    }
    Ok(())
}

fn setup_function_call(
    func_name: &str,
    args: &[SimpleExpr],
    new_fp_pos: usize,
    return_label: &Label,
    compiler: &Compiler,
) -> Result<Vec<IntermediateInstruction>, String> {
    let mut instructions = vec![
        IntermediateInstruction::RequestMemory {
            offset: new_fp_pos.into(),
            size: ConstExpression::function_size(Label::function(func_name)).into(),
            vectorized: false,
            vectorized_len: IntermediateValue::Constant(ConstExpression::zero()),
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::zero(),
            res: IntermediaryMemOrFpOrConstant::Constant(ConstExpression::label(
                return_label.clone(),
            )),
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::one(),
            res: IntermediaryMemOrFpOrConstant::Fp,
        },
    ];

    // Copy arguments
    for (i, arg) in args.iter().enumerate() {
        instructions.push(IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: (2 + i).into(),
            res: arg.to_mem_after_fp_or_constant(compiler),
        });
    }

    instructions.push(IntermediateInstruction::Jump {
        dest: IntermediateValue::label(Label::function(func_name)),
        updated_fp: Some(IntermediateValue::MemoryAfterFp {
            offset: new_fp_pos.into(),
        }),
    });

    Ok(instructions)
}

fn compile_poseidon(
    instructions: &mut Vec<IntermediateInstruction>,
    args: &[SimpleExpr],
    compiler: &Compiler,
    over_16: bool, // otherwise over_24
) -> Result<(), String> {
    assert_eq!(args.len(), 3);

    let low_level_arg_a = IntermediateValue::from_simple_expr(&args[0], compiler);
    let low_level_arg_b = IntermediateValue::from_simple_expr(&args[1], compiler);
    let low_level_res = IntermediateValue::from_simple_expr(&args[2], compiler);

    if over_16 {
        instructions.push(IntermediateInstruction::Poseidon2_16 {
            arg_a: low_level_arg_a,
            arg_b: low_level_arg_b,
            res: low_level_res,
        });
    } else {
        instructions.push(IntermediateInstruction::Poseidon2_24 {
            arg_a: low_level_arg_a,
            arg_b: low_level_arg_b,
            res: low_level_res,
        });
    }

    Ok(())
}

fn compile_function_ret(
    instructions: &mut Vec<IntermediateInstruction>,
    return_data: &[SimpleExpr],
    compiler: &Compiler,
) {
    for (i, ret_var) in return_data.iter().enumerate() {
        instructions.push(IntermediateInstruction::equality(
            IntermediateValue::MemoryAfterFp {
                offset: (2 + compiler.args_count + i).into(),
            },
            IntermediateValue::from_simple_expr(ret_var, compiler),
        ));
    }
    instructions.push(IntermediateInstruction::Jump {
        dest: IntermediateValue::MemoryAfterFp { offset: 0.into() },
        updated_fp: Some(IntermediateValue::MemoryAfterFp { offset: 1.into() }),
    });
}
