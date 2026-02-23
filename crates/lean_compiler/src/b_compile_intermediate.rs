use crate::{a_simplify_lang::*, ir::*, lang::*};
use lean_vm::*;
use std::collections::{BTreeMap, BTreeSet};
use utils::ToUsize;

#[derive(Default)]
struct Compiler {
    bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    match_blocks: Vec<MatchBlock>,
    if_counter: usize,
    call_counter: usize,
    match_counter: usize,
    func_name: String,
    stack_frame_layout: StackFrameLayout,
    args_count: usize,
    stack_size: usize,
    stack_pos: usize,
    const_mallocs: BTreeMap<ConstMallocLabel, usize>, // label -> start offset from fp
    const_malloc_vars: BTreeMap<Var, isize>, // var -> start offset from fp (can be negative for intermediate derived vars)
    dead_fp_relative_vars: BTreeSet<Var>,    // vars whose pointer-storing ADD is dead
    dead_store_vars: BTreeSet<Var>,          // vars that are never used as runtime operands
}

#[derive(Default)]
struct StackFrameLayout {
    // Innermost lexical scope last
    scopes: Vec<ScopeLayout>,
}

#[derive(Default)]
struct ScopeLayout {
    var_positions: BTreeMap<Var, usize>, // var -> memory offset from fp
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

    fn register_var_if_needed(&mut self, var: &Var) {
        if !self.is_in_scope(var) {
            let scope = self.stack_frame_layout.scopes.last_mut().unwrap();
            scope.var_positions.insert(var.clone(), self.stack_pos);
            self.stack_pos += 1;
        }
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
                let base = self.const_mallocs.get(malloc_label).unwrap_or_else(|| {
                    panic!("Const malloc {malloc_label} not in scope");
                });
                ConstExpression::MathExpr(MathOperation::Add, vec![(*base).into(), offset.clone()])
            }
        }
    }
}

impl IntermediateValue {
    fn from_simple_expr(expr: &SimpleExpr, compiler: &Compiler) -> Self {
        match expr {
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => Self::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
            SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset }) => {
                Self::MemoryAfterFp {
                    offset: compiler.get_offset(&VarOrConstMallocAccess::ConstMallocAccess {
                        malloc_label: *malloc_label,
                        offset: offset.clone(),
                    }),
                }
            }
            SimpleExpr::Constant(c) => Self::Constant(c.clone()),
        }
    }
}

/// Try to encode a precompile arg as FpRelative (fp + known_offset).
/// Works for const_malloc vars and derived fp-relative vars (const_malloc + constant).
fn try_precompile_fp_relative(expr: &SimpleExpr, compiler: &Compiler) -> Option<IntermediateValue> {
    if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = expr {
        compiler
            .const_malloc_vars
            .get(var)
            .filter(|&&offset| offset >= 0)
            .map(|&start| IntermediateValue::FpRelative {
                offset: (start as usize).into(),
            })
    } else {
        None
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
    compiler.const_mallocs.clear();
    compiler.const_malloc_vars.clear();
    compiler.dead_fp_relative_vars = compute_dead_fp_relative_vars(&function.instructions);
    compiler.dead_store_vars = compute_dead_store_vars(&function.instructions);

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
                if !compiler.dead_fp_relative_vars.contains(var) && !compiler.dead_store_vars.contains(var) {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }
            }

            SimpleLine::Assignment {
                var,
                operation,
                arg0,
                arg1,
            } => {
                // Track derived fp-relative variables: if result = fp_relative_var +/- constant,
                // then the result is also fp-relative (e.g. `ptr = arr + 8` or `ptr = arr - 1`)
                let mut is_dead_derived = false;
                if let VarOrConstMallocAccess::Var(v) = var
                    && (*operation == MathOperation::Add || *operation == MathOperation::Sub)
                {
                    let fp_offset = match (operation, arg0, arg1) {
                        // Add: commutative, either order
                        (
                            MathOperation::Add,
                            SimpleExpr::Memory(VarOrConstMallocAccess::Var(x)),
                            SimpleExpr::Constant(c),
                        )
                        | (
                            MathOperation::Add,
                            SimpleExpr::Constant(c),
                            SimpleExpr::Memory(VarOrConstMallocAccess::Var(x)),
                        ) => compiler
                            .const_malloc_vars
                            .get(x)
                            .and_then(|&base| c.naive_eval().map(|f| base + f.to_usize() as isize)),
                        // Sub: only var - constant
                        (
                            MathOperation::Sub,
                            SimpleExpr::Memory(VarOrConstMallocAccess::Var(x)),
                            SimpleExpr::Constant(c),
                        ) => compiler
                            .const_malloc_vars
                            .get(x)
                            .and_then(|&base| c.naive_eval().map(|f| base - f.to_usize() as isize)),
                        _ => None,
                    };
                    if let Some(offset) = fp_offset {
                        compiler.const_malloc_vars.insert(v.clone(), offset);
                        is_dead_derived = compiler.dead_fp_relative_vars.contains(v);
                    }
                }

                if is_dead_derived {
                    // No slot needed: all uses go through const_malloc_vars, not var_positions
                    continue;
                }

                // Skip assignments to vars that are never used as runtime operands
                if let VarOrConstMallocAccess::Var(v) = var
                    && compiler.dead_store_vars.contains(v)
                {
                    continue;
                }

                if let VarOrConstMallocAccess::Var(var) = var {
                    compiler.register_var_if_needed(var);
                }

                let arg0 = IntermediateValue::from_simple_expr(arg0, compiler);
                let arg1 = IntermediateValue::from_simple_expr(arg1, compiler);

                instructions.push(IntermediateInstruction::computation(
                    *operation,
                    arg0,
                    arg1,
                    IntermediateValue::from_simple_expr(&var.clone().into(), compiler),
                ));
            }

            SimpleLine::AssertZero { operation, arg0, arg1 } => {
                instructions.push(IntermediateInstruction::computation(
                    *operation,
                    IntermediateValue::from_simple_expr(arg0, compiler),
                    IntermediateValue::from_simple_expr(arg1, compiler),
                    IntermediateValue::Constant(0.into()),
                ));
            }

            SimpleLine::Match { value, arms, offset } => {
                compiler.stack_frame_layout.scopes.push(ScopeLayout::default());

                let label_id = compiler.match_counter;
                compiler.match_counter += 1;
                let end_label = Label::match_end(label_id);

                let value_simplified = IntermediateValue::from_simple_expr(value, compiler);

                let mut compiled_arms = vec![];
                let saved_stack_pos = compiler.stack_pos;
                let mut new_stack_pos = saved_stack_pos;
                for arm in arms.iter() {
                    compiler.stack_pos = saved_stack_pos;
                    compiler.stack_frame_layout.scopes.push(ScopeLayout::default());
                    let arm_instructions = compile_lines(function_name, arm, compiler, Some(end_label.clone()))?;
                    compiled_arms.push(arm_instructions);
                    compiler.stack_frame_layout.scopes.pop();
                    new_stack_pos = new_stack_pos.max(compiler.stack_pos);
                }
                compiler.stack_pos = new_stack_pos;
                compiler.match_blocks.push(MatchBlock {
                    function_name: function_name.clone(),
                    match_cases: compiled_arms,
                });
                // Get the actual index AFTER pushing (nested matches may have pushed their blocks first)
                let match_index = compiler.match_blocks.len() - 1;

                let value_scaled_offset = IntermediateValue::MemoryAfterFp {
                    offset: compiler.stack_pos.into(),
                };
                compiler.stack_pos += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Mul,
                    arg_a: value_simplified,
                    arg_b: ConstExpression::Value(ConstantValue::MatchBlockSize { match_index }).into(),
                    res: value_scaled_offset.clone(),
                });

                // MatchFirstBlockStart - offset * MatchBlockSize
                let base_address = ConstExpression::MathExpr(
                    MathOperation::Sub,
                    vec![
                        ConstExpression::Value(ConstantValue::MatchFirstBlockStart { match_index }),
                        ConstExpression::MathExpr(
                            MathOperation::Mul,
                            vec![
                                ConstExpression::from(*offset),
                                ConstExpression::Value(ConstantValue::MatchBlockSize { match_index }),
                            ],
                        ),
                    ],
                );

                let jump_dest_offset = IntermediateValue::MemoryAfterFp {
                    offset: compiler.stack_pos.into(),
                };
                compiler.stack_pos += 1;
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Add,
                    arg_a: value_scaled_offset,
                    arg_b: base_address.into(),
                    res: jump_dest_offset.clone(),
                });
                instructions.push(IntermediateInstruction::Jump {
                    dest: jump_dest_offset,
                    updated_fp: None,
                });

                let remaining = compile_lines(function_name, &lines[i + 1..], compiler, final_jump)?;
                compiler.bytecode.insert(end_label, remaining);

                compiler.stack_frame_layout.scopes.pop();
                // Don't reset stack_pos here - we need to preserve space for the temps we allocated.
                // Nested matches would otherwise reuse the same temp positions, causing conflicts.
                // This is consistent with IfNotZero which also doesn't reset stack_pos.

                return Ok(instructions);
            }

            SimpleLine::IfNotZero {
                condition,
                then_branch,
                else_branch,
                location,
            } => {
                let if_id = compiler.if_counter;
                compiler.if_counter += 1;

                let (if_label, else_label, end_label) = (
                    Label::if_label(if_id, *location),
                    Label::else_label(if_id, *location),
                    Label::if_else_end(if_id, *location),
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
                    arg_b: IntermediateValue::MemoryAfterFp {
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
                    arg_b: IntermediateValue::MemoryAfterFp {
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
                    arg_b: condition_simplified,
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
                if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = res {
                    compiler.register_var_if_needed(var);
                }
                let shift_0 = match index {
                    SimpleExpr::Constant(c) => c.clone(),
                    _ => compiler.get_offset(&index.clone().try_into().unwrap()),
                };
                instructions.push(IntermediateInstruction::Deref {
                    shift_0,
                    shift_1: shift.clone(),
                    res: IntermediateValue::from_simple_expr(res, compiler),
                });
            }

            SimpleLine::FunctionCall {
                function_name: callee_function_name,
                args,
                return_data,
                location,
            } => {
                let call_id = compiler.call_counter;
                compiler.call_counter += 1;
                let return_label = Label::return_from_call(call_id, *location);
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
                    compiler.register_var_if_needed(var);
                }

                let after_call = {
                    let mut instructions = Vec::new();

                    // Copy return values
                    for (i, ret_var) in return_data.iter().enumerate() {
                        instructions.push(IntermediateInstruction::Deref {
                            shift_0: new_fp_pos.into(),
                            shift_1: (2 + args.len() + i).into(),
                            res: IntermediateValue::MemoryAfterFp {
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
                match table {
                    Table::ExtensionOp(_) => assert_eq!(args.len(), 5),
                    Table::Poseidon16(_) => assert_eq!(args.len(), 3),
                    Table::Execution(_) => unreachable!(),
                }
                // if arg_c is constant, create a variable (in memory) to hold it
                let arg_c = if let SimpleExpr::Constant(cst) = &args[2] {
                    instructions.push(IntermediateInstruction::Computation {
                        operation: Operation::Add,
                        arg_a: IntermediateValue::Constant(cst.clone()),
                        arg_b: IntermediateValue::Constant(0.into()),
                        res: IntermediateValue::MemoryAfterFp {
                            offset: compiler.stack_pos.into(),
                        },
                    });
                    let offset = compiler.stack_pos;
                    compiler.stack_pos += 1;
                    IntermediateValue::MemoryAfterFp { offset: offset.into() }
                } else {
                    try_precompile_fp_relative(&args[2], compiler)
                        .unwrap_or_else(|| IntermediateValue::from_simple_expr(&args[2], compiler))
                };
                let (arg_a, arg_b) = match (
                    try_precompile_fp_relative(&args[0], compiler),
                    try_precompile_fp_relative(&args[1], compiler),
                ) {
                    (Some(a), Some(b)) => (a, b),
                    _ => (
                        IntermediateValue::from_simple_expr(&args[0], compiler),
                        IntermediateValue::from_simple_expr(&args[1], compiler),
                    ),
                };
                instructions.push(IntermediateInstruction::Precompile {
                    table: *table,
                    arg_a,
                    arg_b,
                    arg_c,
                    aux_1: args.get(3).unwrap_or(&SimpleExpr::zero()).as_constant().unwrap(),
                    aux_2: args.get(4).unwrap_or(&SimpleExpr::zero()).as_constant().unwrap(),
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
                        arg_b: IntermediateValue::Constant(0.into()),
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
            SimpleLine::Panic { message } => {
                instructions.push(IntermediateInstruction::PanicHint {
                    message: message.clone(),
                });
                instructions.push(IntermediateInstruction::Panic);
            }
            SimpleLine::HintMAlloc { var, size } => {
                compiler.register_var_if_needed(var);
                instructions.push(IntermediateInstruction::RequestMemory {
                    offset: compiler.get_offset(&var.clone().into()),
                    size: IntermediateValue::from_simple_expr(size, compiler),
                });
            }
            SimpleLine::ConstMalloc { var, size, label } => {
                let size = size.naive_eval().unwrap().to_usize();
                if !compiler.dead_fp_relative_vars.contains(var) {
                    compiler.register_var_if_needed(var);
                }
                handle_const_malloc(&mut instructions, compiler, var, size, label);
            }
            SimpleLine::CustomHint(hint, args) => {
                let simplified_args = args
                    .iter()
                    .map(|expr| IntermediateValue::from_simple_expr(expr, compiler))
                    .collect::<Vec<_>>();
                instructions.push(IntermediateInstruction::CustomHint(*hint, simplified_args));
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
            SimpleLine::DebugAssert(boolean, location) => {
                let boolean_simplified = BooleanExpr {
                    kind: boolean.kind,
                    left: IntermediateValue::from_simple_expr(&boolean.left, compiler),
                    right: IntermediateValue::from_simple_expr(&boolean.right, compiler),
                };
                instructions.push(IntermediateInstruction::DebugAssert(boolean_simplified, *location));
            }
            SimpleLine::RangeCheck { val, bound } => {
                // Range check for val <= bound compiles to:
                // 1. DEREF: m[fp + aux1] = m[m[fp + val_offset]] - proves val < M
                // 2. ADD: m[fp + val_offset] + m[fp + aux2] = bound - computes complement
                // 3. DEREF: m[fp + aux3] = m[m[fp + aux2]] - proves complement < M
                //
                // DerefHint records constraints: memory[target] = memory[memory[src]]
                // These are resolved at end of execution in correct order.

                // Get the offset of the value being range-checked
                let val_offset = match val {
                    SimpleExpr::Memory(var_or_const) => compiler.get_offset(var_or_const),
                    SimpleExpr::Constant(val_const) => {
                        // For constants, we need to store in a temp variable first
                        let temp_offset = compiler.stack_pos;
                        compiler.stack_pos += 1;
                        instructions.push(IntermediateInstruction::Computation {
                            operation: Operation::Add,
                            arg_a: IntermediateValue::Constant(val_const.clone()),
                            arg_b: IntermediateValue::Constant(ConstExpression::zero()),
                            res: IntermediateValue::MemoryAfterFp {
                                offset: ConstExpression::from_usize(temp_offset),
                            },
                        });
                        ConstExpression::from_usize(temp_offset)
                    }
                };

                // Allocate 3 auxiliary cells
                let aux1_offset = ConstExpression::from_usize(compiler.stack_pos);
                compiler.stack_pos += 1;
                let aux2_offset = ConstExpression::from_usize(compiler.stack_pos);
                compiler.stack_pos += 1;
                let aux3_offset = ConstExpression::from_usize(compiler.stack_pos);
                compiler.stack_pos += 1;

                // DerefHint for first DEREF: memory[aux1] = memory[memory[val_offset]]
                instructions.push(IntermediateInstruction::DerefHint {
                    offset_src: val_offset.clone(),
                    offset_target: aux1_offset.clone(),
                });

                // 1. DEREF: m[fp + aux1] = m[m[fp + val_offset]]
                instructions.push(IntermediateInstruction::Deref {
                    shift_0: val_offset.clone(),
                    shift_1: ConstExpression::zero(),
                    res: IntermediateValue::MemoryAfterFp { offset: aux1_offset },
                });

                // 2. ADD: m[fp + val_offset] + m[fp + aux2] = bound
                let bound_value = IntermediateValue::from_simple_expr(bound, compiler);
                instructions.push(IntermediateInstruction::Computation {
                    operation: Operation::Add,
                    arg_a: IntermediateValue::MemoryAfterFp {
                        offset: val_offset.clone(),
                    },
                    arg_b: IntermediateValue::MemoryAfterFp {
                        offset: aux2_offset.clone(),
                    },
                    res: bound_value,
                });

                // DerefHint for second DEREF: memory[aux3] = memory[memory[aux2]]
                instructions.push(IntermediateInstruction::DerefHint {
                    offset_src: aux2_offset.clone(),
                    offset_target: aux3_offset.clone(),
                });

                // 3. DEREF: m[fp + aux3] = m[m[fp + aux2]]
                instructions.push(IntermediateInstruction::Deref {
                    shift_0: aux2_offset,
                    shift_1: ConstExpression::zero(),
                    res: IntermediateValue::MemoryAfterFp { offset: aux3_offset },
                });
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
    compiler.const_mallocs.insert(*label, compiler.stack_pos);
    compiler
        .const_malloc_vars
        .insert(var.clone(), compiler.stack_pos as isize);
    if !compiler.dead_fp_relative_vars.contains(var) {
        instructions.push(IntermediateInstruction::Computation {
            operation: Operation::Add,
            arg_a: IntermediateValue::Constant(compiler.stack_pos.into()),
            arg_b: IntermediateValue::FpRelative {
                offset: ConstExpression::zero(),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
        });
    }
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
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::zero(),
            res: IntermediateValue::Constant(ConstExpression::label(return_label.clone())),
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::one(),
            res: IntermediateValue::FpRelative {
                offset: ConstExpression::zero(),
            },
        },
    ];

    // Copy arguments
    for (i, arg) in args.iter().enumerate() {
        instructions.push(IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: (2 + i).into(),
            res: IntermediateValue::from_simple_expr(arg, compiler),
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
