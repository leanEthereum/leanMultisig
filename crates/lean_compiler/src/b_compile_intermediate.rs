use crate::{F, a_simplify_lang::*, ir::*, lang::*};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use std::collections::{BTreeMap, BTreeSet};
use utils::ToUsize;

#[derive(Default)]
struct Compiler {
    bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    match_blocks: Vec<MatchBlock>,
    if_counter: usize,
    call_counter: usize,
    func_name: String,
    stack_frame_layout: StackFrameLayout,
    args_count: usize,
    stack_size: usize,
    stack_pos: usize,
}

#[derive(Default)]
struct StackFrameLayout {
    // Innermost lexical scope last
    scopes: Vec<ScopeLayout>,
}

#[derive(Default)]
struct ScopeLayout {
    var_positions: BTreeMap<Var, usize>,              // var -> memory offset from fp
    const_mallocs: BTreeMap<ConstMallocLabel, usize>, // const_malloc_label -> start = memory offset from fp
}

impl Compiler {
    fn is_in_scope(&self, var: &Var) -> bool {
        for scope in self.stack_frame_layout.scopes.iter() {
            if let Some(_offset) = scope.var_positions.get(var) {
                return true;
            }
        }
        false
    }

    fn get_offset(&self, var: &VarOrConstMallocAccess) -> ConstExpression {
        match var {
            VarOrConstMallocAccess::Var(var) => {
                for scope in self.stack_frame_layout.scopes.iter().rev() {
                    if let Some(offset) = scope.var_positions.get(var) {
                        return (*offset).into();
                    }
                }
                panic!("Variable {var} not in scope");
            }
            VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset } => {
                for scope in self.stack_frame_layout.scopes.iter().rev() {
                    if let Some(base) = scope.const_mallocs.get(malloc_label) {
                        return ConstExpression::Binary {
                            left: Box::new((*base).into()),
                            operation: HighLevelOperation::Add,
                            right: Box::new((*offset).clone()),
                        };
                    }
                }
                panic!("Const malloc {malloc_label} not in scope");
            }
        }
    }
}

impl SimpleExpr {
    fn to_mem_after_fp_or_constant(&self, compiler: &Compiler) -> IntermediaryMemOrFpOrConstant {
        match self {
            Self::Var(var) => IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
            Self::Constant(c) => IntermediaryMemOrFpOrConstant::Constant(c.clone()),
            Self::ConstMallocAccess { malloc_label, offset } => IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                offset: compiler.get_offset(&VarOrConstMallocAccess::ConstMallocAccess {
                    malloc_label: *malloc_label,
                    offset: offset.clone(),
                }),
            },
        }
    }
}

impl IntermediateValue {
    fn from_simple_expr(expr: &SimpleExpr, compiler: &Compiler) -> Self {
        match expr {
            SimpleExpr::Var(var) => Self::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
            SimpleExpr::Constant(c) => Self::Constant(c.clone()),
            SimpleExpr::ConstMallocAccess { malloc_label, offset } => Self::MemoryAfterFp {
                offset: compiler.get_offset(&VarOrConstMallocAccess::ConstMallocAccess {
                    malloc_label: *malloc_label,
                    offset: offset.clone(),
                }),
            },
        }
    }

    fn from_var_or_const_malloc_access(var_or_const: &VarOrConstMallocAccess, compiler: &Compiler) -> Self {
        Self::from_simple_expr(&var_or_const.clone().into(), compiler)
    }
}

pub fn compile_to_intermediate_bytecode(simple_program: SimpleProgram) -> Result<IntermediateBytecode, String> {
    let mut compiler = Compiler::default();
    let mut memory_sizes = BTreeMap::new();

    for function in simple_program.functions.values() {
        let instructions = compile_function(function, &mut compiler)?;
        compiler.bytecode.insert(Label::function(&function.name), instructions);
        memory_sizes.insert(function.name.clone(), compiler.stack_size);
    }

    Ok(IntermediateBytecode {
        bytecode: compiler.bytecode,
        match_blocks: compiler.match_blocks,
        memory_size_per_function: memory_sizes,
    })
}

fn compile_function(
    function: &SimpleFunction,
    compiler: &mut Compiler,
) -> Result<Vec<IntermediateInstruction>, String> {
    // memory layout: pc, fp, args, return_vars, internal_vars
    let mut stack_pos = 2; // Reserve space for pc and fp
    let function_scope_layout = ScopeLayout::default();
    compiler.stack_frame_layout = StackFrameLayout {
        scopes: vec![function_scope_layout],
    };
    let function_scope_layout = &mut compiler.stack_frame_layout.scopes[0];

    for (i, var) in function.arguments.iter().enumerate() {
        function_scope_layout.var_positions.insert(var.clone(), stack_pos + i);
    }
    stack_pos += function.arguments.len();

    stack_pos += function.n_returned_vars;

    compiler.func_name = function.name.clone();
    compiler.stack_pos = stack_pos;
    compiler.stack_size = stack_pos;
    compiler.args_count = function.arguments.len();

    compile_lines(
        &Label::function(function.name.clone()),
        &function.instructions,
        compiler,
        None,
    )
}

fn compile_lines(
    function_name: &Label,
    lines: &[SimpleLine],
    compiler: &mut Compiler,
    final_jump: Option<Label>,
) -> Result<Vec<IntermediateInstruction>, String> {
    let mut instructions = Vec::new();

    for (i, line) in lines.iter().enumerate() {
        match line {
            SimpleLine::ForwardDeclaration { var } => {
                let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                current_scope_layout
                    .var_positions
                    .insert(var.clone(), compiler.stack_pos);
                compiler.stack_pos += 1;
            }

            SimpleLine::Assignment {
                var,
                operation,
                arg0,
                arg1,
            } => {
                let arg0 = IntermediateValue::from_simple_expr(arg0, compiler);
                let arg1 = IntermediateValue::from_simple_expr(arg1, compiler);

                if let VarOrConstMallocAccess::Var(var) = var
                    && !compiler.is_in_scope(var)
                {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }

                instructions.push(IntermediateInstruction::computation(
                    *operation,
                    arg0,
                    arg1,
                    IntermediateValue::from_var_or_const_malloc_access(var, compiler),
                ));
            }

            SimpleLine::TestZero { operation, arg0, arg1 } => {
                instructions.push(IntermediateInstruction::computation(
                    *operation,
                    IntermediateValue::from_simple_expr(arg0, compiler),
                    IntermediateValue::from_simple_expr(arg1, compiler),
                    IntermediateValue::Constant(0.into()),
                ));
            }

            SimpleLine::Match { value, arms } => {
                compiler.stack_frame_layout.scopes.push(ScopeLayout::default());

                let match_index = compiler.match_blocks.len();
                let end_label = Label::match_end(match_index);

                let value_simplified = IntermediateValue::from_simple_expr(value, compiler);

                let mut compiled_arms = vec![];
                let saved_stack_pos = compiler.stack_pos;
                let mut new_stack_pos = saved_stack_pos;
                for arm in arms.iter() {
                    compiler.stack_pos = saved_stack_pos;
                    let arm_instructions = compile_lines(function_name, arm, compiler, Some(end_label.clone()))?;
                    compiled_arms.push(arm_instructions);
                    new_stack_pos = new_stack_pos.max(compiler.stack_pos);
                }
                compiler.stack_pos = new_stack_pos;
                compiler.match_blocks.push(MatchBlock {
                    function_name: function_name.clone(),
                    match_cases: compiled_arms,
                });

                let value_scaled_offset = IntermediateValue::MemoryAfterFp {
                    offset: compiler.stack_pos.into(),
                };
                compiler.stack_pos += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Mul,
                    arg_a: value_simplified,
                    arg_c: ConstExpression::Value(ConstantValue::MatchBlockSize { match_index }).into(),
                    res: value_scaled_offset.clone(),
                });

                let jump_dest_offset = IntermediateValue::MemoryAfterFp {
                    offset: compiler.stack_pos.into(),
                };
                compiler.stack_pos += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Add,
                    arg_a: value_scaled_offset,
                    arg_c: ConstExpression::Value(ConstantValue::MatchFirstBlockStart { match_index }).into(),
                    res: jump_dest_offset.clone(),
                });
                instructions.push(IntermediateInstruction::Jump {
                    dest: jump_dest_offset,
                    updated_fp: None,
                });

                let remaining = compile_lines(function_name, &lines[i + 1..], compiler, final_jump)?;
                compiler.bytecode.insert(end_label, remaining);

                compiler.stack_frame_layout.scopes.pop();
                compiler.stack_pos = saved_stack_pos;
                // It is not necessary to update compiler.stack_size here because the preceding call to
                // compile lines should have done so.

                return Ok(instructions);
            }

            SimpleLine::IfNotZero {
                condition,
                then_branch,
                else_branch,
                line_number,
            } => {
                let if_id = compiler.if_counter;
                compiler.if_counter += 1;

                let (if_label, else_label, end_label) = (
                    Label::if_label(if_id, *line_number),
                    Label::else_label(if_id, *line_number),
                    Label::if_else_end(if_id, *line_number),
                );

                // c: condition
                let condition_simplified = IntermediateValue::from_simple_expr(condition, compiler);

                // 1/c (or 0 if c is zero)
                let condition_inverse_offset = compiler.stack_pos;
                compiler.stack_pos += 1;
                instructions.push(IntermediateInstruction::Inverse {
                    arg: condition_simplified.clone(),
                    res_offset: condition_inverse_offset,
                });

                // c x 1/c
                let product_offset = compiler.stack_pos;
                compiler.stack_pos += 1;
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
                // It is not necessary to update compiler.stack_size here because the preceding call to
                // compile lines should have done so.

                // 1 - (c x 1/c)
                let one_minus_product_offset = compiler.stack_pos;
                compiler.stack_pos += 1;
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

                let saved_stack_pos = compiler.stack_pos;

                compiler.stack_frame_layout.scopes.push(ScopeLayout::default());
                let then_instructions = compile_lines(function_name, then_branch, compiler, Some(end_label.clone()))?;

                let then_stack_pos = compiler.stack_pos;
                compiler.stack_pos = saved_stack_pos;
                compiler.stack_frame_layout.scopes.pop();
                compiler.stack_frame_layout.scopes.push(ScopeLayout::default());

                let else_instructions = compile_lines(function_name, else_branch, compiler, Some(end_label.clone()))?;

                compiler.bytecode.insert(if_label, then_instructions);
                compiler.bytecode.insert(else_label, else_instructions);

                compiler.stack_frame_layout.scopes.pop();
                compiler.stack_pos = compiler.stack_pos.max(then_stack_pos);

                let remaining = compile_lines(function_name, &lines[i + 1..], compiler, final_jump)?;
                compiler.bytecode.insert(end_label, remaining);
                // It is not necessary to update compiler.stack_size here because the preceding call to
                // compile_lines should have done so.

                return Ok(instructions);
            }

            SimpleLine::RawAccess { res, index, shift } => {
                if let SimpleExpr::Var(var) = res
                    && !compiler.is_in_scope(var)
                {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
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
                function_name: callee_function_name,
                args,
                return_data,
                line_number,
            } => {
                let call_id = compiler.call_counter;
                compiler.call_counter += 1;
                let return_label = Label::return_from_call(call_id, *line_number);

                let new_fp_pos = compiler.stack_pos;
                compiler.stack_pos += 1;

                instructions.extend(setup_function_call(
                    callee_function_name,
                    args,
                    new_fp_pos,
                    &return_label,
                    compiler,
                )?);

                for var in return_data.iter() {
                    if !compiler.is_in_scope(var) {
                        let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                        current_scope_layout
                            .var_positions
                            .insert(var.clone(), compiler.stack_pos);
                        compiler.stack_pos += 1;
                    }
                }

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

                    instructions.extend(compile_lines(function_name, &lines[i + 1..], compiler, final_jump)?);

                    instructions
                };

                compiler.bytecode.insert(return_label, after_call);
                // It is not necessary to update compiler.stack_size here because the preceding call to
                // compile_lines should have done so.

                return Ok(instructions);
            }

            SimpleLine::Precompile { table, args, .. } => {
                if *table == Table::poseidon24_mem() {
                    assert_eq!(args.len(), 3);
                } else {
                    assert_eq!(args.len(), 4);
                }
                instructions.push(IntermediateInstruction::Precompile {
                    table: *table,
                    arg_a: IntermediateValue::from_simple_expr(&args[0], compiler),
                    arg_b: IntermediateValue::from_simple_expr(&args[1], compiler),
                    arg_c: IntermediateValue::from_simple_expr(&args[2], compiler),
                    aux: args.get(3).unwrap_or(&SimpleExpr::zero()).as_constant().unwrap(),
                });
            }

            SimpleLine::FunctionRet { return_data } => {
                if compiler.func_name == "main" {
                    // pc -> ending_pc, fp -> 0
                    let zero_value_offset = IntermediateValue::MemoryAfterFp {
                        offset: compiler.stack_pos.into(),
                    };
                    compiler.stack_pos += 1;
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
                if !compiler.is_in_scope(var) {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }
                instructions.push(IntermediateInstruction::RequestMemory {
                    offset: compiler.get_offset(&var.clone().into()),
                    size: IntermediateValue::from_simple_expr(size, compiler),
                    vectorized: *vectorized,
                    vectorized_len: IntermediateValue::from_simple_expr(vectorized_len, compiler),
                });
            }
            SimpleLine::ConstMalloc { var, size, label } => {
                let size = size.naive_eval().unwrap().to_usize(); // TODO not very good;
                if !compiler.is_in_scope(var) {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }
                handle_const_malloc(&mut instructions, compiler, var, size, label);
            }
            SimpleLine::DecomposeBits {
                var,
                to_decompose,
                label,
            } => {
                if !compiler.is_in_scope(var) {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }

                instructions.push(IntermediateInstruction::DecomposeBits {
                    res_offset: compiler.stack_pos,
                    to_decompose: to_decompose
                        .iter()
                        .map(|expr| IntermediateValue::from_simple_expr(expr, compiler))
                        .collect(),
                });

                handle_const_malloc(&mut instructions, compiler, var, F::bits() * to_decompose.len(), label);
            }
            SimpleLine::DecomposeCustom { args } => {
                assert!(args.len() >= 3);
                let decomposed = IntermediateValue::from_simple_expr(&args[0], compiler);
                let remaining = IntermediateValue::from_simple_expr(&args[1], compiler);
                instructions.push(IntermediateInstruction::DecomposeCustom {
                    decomposed,
                    remaining,
                    to_decompose: args[2..]
                        .iter()
                        .map(|expr| IntermediateValue::from_simple_expr(expr, compiler))
                        .collect(),
                });
            }
            SimpleLine::PrivateInputStart { result } => {
                if !compiler.is_in_scope(result) {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(result.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }
                instructions.push(IntermediateInstruction::PrivateInputStart {
                    res_offset: compiler.get_offset(&result.clone().into()),
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
                instructions.push(IntermediateInstruction::LocationReport { location: *location });
            }
        }
    }

    compiler.stack_size = compiler.stack_size.max(compiler.stack_pos);

    if let Some(jump_label) = final_jump {
        instructions.push(IntermediateInstruction::Jump {
            dest: IntermediateValue::label(jump_label),
            updated_fp: None,
        });
    }

    Ok(instructions)
}

fn handle_const_malloc(
    instructions: &mut Vec<IntermediateInstruction>,
    compiler: &mut Compiler,
    var: &Var,
    size: usize,
    label: &ConstMallocLabel,
) {
    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
    current_scope_layout.const_mallocs.insert(*label, compiler.stack_pos);
    instructions.push(IntermediateInstruction::Computation {
        operation: Operation::Add,
        arg_a: IntermediateValue::Constant(compiler.stack_pos.into()),
        arg_c: IntermediateValue::Fp,
        res: IntermediateValue::MemoryAfterFp {
            offset: compiler.get_offset(&var.clone().into()),
        },
    });
    compiler.stack_pos += size;
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
            res: IntermediaryMemOrFpOrConstant::Constant(ConstExpression::label(return_label.clone())),
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

fn find_internal_vars(lines: &[SimpleLine]) -> BTreeSet<Var> {
    let mut internal_vars = BTreeSet::new();
    for line in lines {
        match line {
            SimpleLine::ForwardDeclaration { var } => {
                internal_vars.insert(var.clone());
            }
            SimpleLine::Match { arms, .. } => {
                for arm in arms {
                    internal_vars.extend(find_internal_vars(arm));
                }
            }
            SimpleLine::Assignment { var, .. } => {
                if let VarOrConstMallocAccess::Var(var) = var {
                    internal_vars.insert(var.clone());
                }
            }
            SimpleLine::TestZero { .. } => {}
            SimpleLine::HintMAlloc { var, .. }
            | SimpleLine::ConstMalloc { var, .. }
            | SimpleLine::DecomposeBits { var, .. } => {
                internal_vars.insert(var.clone());
            }
            SimpleLine::PrivateInputStart { result } => {
                internal_vars.insert(result.clone());
            }
            SimpleLine::RawAccess { res, .. } => {
                if let SimpleExpr::Var(var) = res {
                    internal_vars.insert(var.clone());
                }
            }
            SimpleLine::FunctionCall { return_data, .. } => {
                internal_vars.extend(return_data.iter().cloned());
            }
            SimpleLine::IfNotZero {
                then_branch,
                else_branch,
                ..
            } => {
                internal_vars.extend(find_internal_vars(then_branch));
                internal_vars.extend(find_internal_vars(else_branch));
            }
            SimpleLine::Panic
            | SimpleLine::DecomposeCustom { .. }
            | SimpleLine::Print { .. }
            | SimpleLine::FunctionRet { .. }
            | SimpleLine::Precompile { .. }
            | SimpleLine::LocationReport { .. } => {}
        }
    }
    internal_vars
}
