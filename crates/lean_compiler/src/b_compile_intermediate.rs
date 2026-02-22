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
    const_malloc_vars: BTreeMap<Var, usize>,          // var -> start offset from fp (same data, different key)
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

impl SimpleExpr {
    fn to_mem_after_fp_or_constant(&self, compiler: &Compiler) -> IntermediateValue {
        match self {
            Self::Memory(VarOrConstMallocAccess::Var(var)) => IntermediateValue::MemoryAfterFp {
                offset: compiler.get_offset(&var.clone().into()),
            },
            Self::Memory(VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset }) => {
                IntermediateValue::MemoryAfterFp {
                    offset: compiler.get_offset(&VarOrConstMallocAccess::ConstMallocAccess {
                        malloc_label: *malloc_label,
                        offset: offset.clone(),
                    }),
                }
            }
            Self::Constant(c) => IntermediateValue::Constant(c.clone()),
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

    fn from_var_or_const_malloc_access(var_or_const: &VarOrConstMallocAccess, compiler: &Compiler) -> Self {
        Self::from_simple_expr(&var_or_const.clone().into(), compiler)
    }
}

/// Try to encode a precompile arg as FpRelative (fp + known_offset).
/// Works for const_malloc vars and derived fp-relative vars (const_malloc + constant).
fn try_precompile_fp_relative(expr: &SimpleExpr, compiler: &Compiler) -> Option<IntermediateValue> {
    if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = expr {
        compiler
            .const_malloc_vars
            .get(var)
            .map(|&start| IntermediateValue::FpRelative { offset: start.into() })
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

    compile_lines(
        &Label::function(function.name.clone()),
        &function.instructions,
        compiler,
        None,
    )
}

/// Count how many times each Var is used (read, not defined) in the given lines.
/// Includes uses in nested blocks (Match arms, IfNotZero branches).
fn count_var_uses(lines: &[SimpleLine]) -> BTreeMap<Var, usize> {
    let mut counts = BTreeMap::new();
    fn count_expr(expr: &SimpleExpr, counts: &mut BTreeMap<Var, usize>) {
        if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)) = expr {
            *counts.entry(v.clone()).or_default() += 1;
        }
    }
    fn count_lines(lines: &[SimpleLine], counts: &mut BTreeMap<Var, usize>) {
        for line in lines {
            match line {
                SimpleLine::Assignment { arg0, arg1, .. } => {
                    count_expr(arg0, counts);
                    count_expr(arg1, counts);
                }
                SimpleLine::AssertZero { arg0, arg1, .. } => {
                    count_expr(arg0, counts);
                    count_expr(arg1, counts);
                }
                SimpleLine::RawAccess { res, index, .. } => {
                    count_expr(res, counts);
                    count_expr(index, counts);
                }
                SimpleLine::Precompile { args, .. } => {
                    for arg in args {
                        count_expr(arg, counts);
                    }
                }
                SimpleLine::FunctionCall { args, .. } => {
                    for arg in args {
                        count_expr(arg, counts);
                    }
                }
                SimpleLine::FunctionRet { return_data } => {
                    for expr in return_data {
                        count_expr(expr, counts);
                    }
                }
                SimpleLine::Print { content, .. } => {
                    for expr in content {
                        count_expr(expr, counts);
                    }
                }
                SimpleLine::HintMAlloc { size, .. } => {
                    count_expr(size, counts);
                }
                SimpleLine::CustomHint(_, args) => {
                    for arg in args {
                        count_expr(arg, counts);
                    }
                }
                SimpleLine::Match { value, arms, .. } => {
                    count_expr(value, counts);
                    for arm in arms {
                        count_lines(arm, counts);
                    }
                }
                SimpleLine::IfNotZero {
                    condition,
                    then_branch,
                    else_branch,
                    ..
                } => {
                    count_expr(condition, counts);
                    count_lines(then_branch, counts);
                    count_lines(else_branch, counts);
                }
                SimpleLine::DebugAssert(bool_expr, _) => {
                    count_expr(&bool_expr.left, counts);
                    count_expr(&bool_expr.right, counts);
                }
                SimpleLine::RangeCheck { val, bound } => {
                    count_expr(val, counts);
                    count_expr(bound, counts);
                }
                SimpleLine::ForwardDeclaration { .. }
                | SimpleLine::ConstMalloc { .. }
                | SimpleLine::Panic { .. }
                | SimpleLine::LocationReport { .. } => {}
            }
        }
    }
    count_lines(lines, &mut counts);
    counts
}

fn apply_dead_add_removal(
    instructions: Vec<IntermediateInstruction>,
    dead_add_indices: &BTreeSet<usize>,
) -> Vec<IntermediateInstruction> {
    if dead_add_indices.is_empty() {
        return instructions;
    }
    instructions
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !dead_add_indices.contains(i))
        .map(|(_, instr)| instr)
        .collect()
}

/// Phase 2 of dead ADD removal: mark derived fp-relative ADDs as dead when all uses of
/// the result variable are FpRelative-encoded (no memory load needed). Populates
/// `dead_derived_base_vars` so the next phase can check if base const_malloc ADDs are also dead.
fn mark_dead_derived_adds(
    dead_add_indices: &mut BTreeSet<usize>,
    derived_fp_relative_add_idx: &BTreeMap<Var, (usize, Var)>,
    var_use_counts: &BTreeMap<Var, usize>,
    fp_relative_use_count: &BTreeMap<Var, usize>,
    dead_derived_base_vars: &mut BTreeMap<Var, usize>,
) {
    for (var, (idx, base_var)) in derived_fp_relative_add_idx {
        let total_uses = var_use_counts.get(var).copied().unwrap_or(0);
        let fp_rel_uses = fp_relative_use_count.get(var).copied().unwrap_or(0);
        if total_uses > 0 && total_uses == fp_rel_uses {
            dead_add_indices.insert(*idx);
            *dead_derived_base_vars.entry(base_var.clone()).or_default() += 1;
        }
    }
}

/// Phase 3 of dead ADD removal: mark ConstMalloc ADDs as dead when the stored pointer
/// is never read at runtime. This happens when all uses of the variable are either:
/// - FpRelative precompile args (which encode `fp + offset` directly, not via memory)
/// - Operands in derived fp-relative ADDs that were themselves dead-removed
fn mark_dead_const_malloc_adds(
    dead_add_indices: &mut BTreeSet<usize>,
    const_malloc_add_idx: &BTreeMap<Var, usize>,
    var_use_counts: &BTreeMap<Var, usize>,
    fp_relative_use_count: &BTreeMap<Var, usize>,
    dead_derived_base_vars: &BTreeMap<Var, usize>,
) {
    for (var, &idx) in const_malloc_add_idx {
        let total_uses = var_use_counts.get(var).copied().unwrap_or(0);
        let fp_rel_uses = fp_relative_use_count.get(var).copied().unwrap_or(0);
        let dead_derived_uses = dead_derived_base_vars.get(var).copied().unwrap_or(0);
        if total_uses == fp_rel_uses + dead_derived_uses {
            dead_add_indices.insert(idx);
        }
    }
}

fn compile_lines(
    function_name: &Label,
    lines: &[SimpleLine],
    compiler: &mut Compiler,
    final_jump: Option<Label>,
) -> Result<Vec<IntermediateInstruction>, String> {
    let mut instructions = Vec::new();
    let mut dead_add_indices: BTreeSet<usize> = BTreeSet::new();
    // Maps derived fp-relative vars to (instruction index, base const_malloc var).
    // Local to this invocation: indices reference *this* invocation's `instructions` vector only.
    let mut derived_fp_relative_add_idx: BTreeMap<Var, (usize, Var)> = BTreeMap::new();
    // Maps const_malloc vars to the instruction index of their pointer-storing ADD.
    let mut const_malloc_add_idx: BTreeMap<Var, usize> = BTreeMap::new();
    // How many times each var is used as FpRelative in precompile args.
    let mut fp_relative_use_count: BTreeMap<Var, usize> = BTreeMap::new();
    // How many times each base var appears in dead-removed derived fp-relative ADDs.
    let mut dead_derived_base_vars: BTreeMap<Var, usize> = BTreeMap::new();
    let var_use_counts = count_var_uses(lines);

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
                // Track derived fp-relative variables: if result = fp_relative_var + constant,
                // then the result is also fp-relative (e.g. `ptr = arr + 8` where arr is const_malloc)
                if let VarOrConstMallocAccess::Var(v) = var
                    && *operation == MathOperation::Add
                {
                    let (fp_offset, base_var) = match (arg0, arg1) {
                        (SimpleExpr::Memory(VarOrConstMallocAccess::Var(x)), SimpleExpr::Constant(c))
                        | (SimpleExpr::Constant(c), SimpleExpr::Memory(VarOrConstMallocAccess::Var(x))) => {
                            let offset = compiler
                                .const_malloc_vars
                                .get(x)
                                .and_then(|&base| c.naive_eval().map(|f| base + f.to_usize()));
                            (offset, Some(x.clone()))
                        }
                        _ => (None, None),
                    };
                    if let Some(offset) = fp_offset {
                        compiler.const_malloc_vars.insert(v.clone(), offset);
                        // Record the instruction index and base var so we can remove this ADD later
                        // if it's only used as a FpRelative precompile arg
                        derived_fp_relative_add_idx.insert(v.clone(), (instructions.len(), base_var.unwrap()));
                    }
                }

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

                mark_dead_derived_adds(
                    &mut dead_add_indices,
                    &derived_fp_relative_add_idx,
                    &var_use_counts,
                    &fp_relative_use_count,
                    &mut dead_derived_base_vars,
                );
                mark_dead_const_malloc_adds(
                    &mut dead_add_indices,
                    &const_malloc_add_idx,
                    &var_use_counts,
                    &fp_relative_use_count,
                    &dead_derived_base_vars,
                );
                return Ok(apply_dead_add_removal(instructions, &dead_add_indices));
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

                mark_dead_derived_adds(
                    &mut dead_add_indices,
                    &derived_fp_relative_add_idx,
                    &var_use_counts,
                    &fp_relative_use_count,
                    &mut dead_derived_base_vars,
                );
                mark_dead_const_malloc_adds(
                    &mut dead_add_indices,
                    &const_malloc_add_idx,
                    &var_use_counts,
                    &fp_relative_use_count,
                    &dead_derived_base_vars,
                );
                return Ok(apply_dead_add_removal(instructions, &dead_add_indices));
            }

            SimpleLine::RawAccess { res, index, shift } => {
                if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = res
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

                mark_dead_derived_adds(
                    &mut dead_add_indices,
                    &derived_fp_relative_add_idx,
                    &var_use_counts,
                    &fp_relative_use_count,
                    &mut dead_derived_base_vars,
                );
                mark_dead_const_malloc_adds(
                    &mut dead_add_indices,
                    &const_malloc_add_idx,
                    &var_use_counts,
                    &fp_relative_use_count,
                    &dead_derived_base_vars,
                );
                return Ok(apply_dead_add_removal(instructions, &dead_add_indices));
            }

            SimpleLine::Precompile { table, args, .. } => {
                match table {
                    Table::DotProduct(_) => assert_eq!(args.len(), 5),
                    Table::Poseidon16(_) => assert_eq!(args.len(), 3),
                    Table::Execution(_) => unreachable!(),
                }
                // if arg_c is constant, create a variable (in memory) to hold it
                // Track which args actually used FpRelative, so we can mark their ADDs as dead
                let mut fp_relative_vars: Vec<Var> = vec![];

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
                    let fp_rel = try_precompile_fp_relative(&args[2], compiler);
                    if fp_rel.is_some()
                        && let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = &args[2]
                    {
                        fp_relative_vars.push(var.clone());
                    }
                    fp_rel.unwrap_or_else(|| IntermediateValue::from_simple_expr(&args[2], compiler))
                };
                let (arg_a, arg_b) = match (
                    try_precompile_fp_relative(&args[0], compiler),
                    try_precompile_fp_relative(&args[1], compiler),
                ) {
                    (Some(a), Some(b)) => {
                        // Both are FpRelative — mark both as dead
                        if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = &args[0] {
                            fp_relative_vars.push(var.clone());
                        }
                        if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = &args[1] {
                            fp_relative_vars.push(var.clone());
                        }
                        (a, b)
                    }
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
                // Accumulate FpRelative use counts; dead ADD removal is deferred to finalization
                // so we can compare total uses vs FpRelative uses across the whole block.
                for var in fp_relative_vars {
                    *fp_relative_use_count.entry(var.clone()).or_default() += 1;
                }
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
                });
            }
            SimpleLine::ConstMalloc { var, size, label } => {
                let size = size.naive_eval().unwrap().to_usize();
                if !compiler.is_in_scope(var) {
                    let current_scope_layout = compiler.stack_frame_layout.scopes.last_mut().unwrap();
                    current_scope_layout
                        .var_positions
                        .insert(var.clone(), compiler.stack_pos);
                    compiler.stack_pos += 1;
                }
                const_malloc_add_idx.insert(var.clone(), instructions.len());
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

    mark_dead_derived_adds(
        &mut dead_add_indices,
        &derived_fp_relative_add_idx,
        &var_use_counts,
        &fp_relative_use_count,
        &mut dead_derived_base_vars,
    );
    mark_dead_const_malloc_adds(
        &mut dead_add_indices,
        &const_malloc_add_idx,
        &var_use_counts,
        &fp_relative_use_count,
        &dead_derived_base_vars,
    );
    Ok(apply_dead_add_removal(instructions, &dead_add_indices))
}

fn handle_const_malloc(
    instructions: &mut Vec<IntermediateInstruction>,
    compiler: &mut Compiler,
    var: &Var,
    size: usize,
    label: &ConstMallocLabel,
) {
    compiler.const_mallocs.insert(*label, compiler.stack_pos);
    compiler.const_malloc_vars.insert(var.clone(), compiler.stack_pos);
    instructions.push(IntermediateInstruction::Computation {
        operation: Operation::Add,
        arg_a: IntermediateValue::Constant(compiler.stack_pos.into()),
        arg_b: IntermediateValue::Fp,
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
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::zero(),
            res: IntermediateValue::Constant(ConstExpression::label(return_label.clone())),
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::one(),
            res: IntermediateValue::Fp,
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
