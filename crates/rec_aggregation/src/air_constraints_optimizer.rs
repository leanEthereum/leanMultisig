//! # AIR Constraint Code Generation Optimizer
//!
//! Standalone infrastructure to find optimal zkDSL instruction sequences for AIR constraints.
//!
//! ## Problem
//!
//! Given a set of symbolic constraint expressions (DAGs of Add/Sub/Mul/Neg over Variables and
//! Constants), emit zkDSL instructions that minimize total cost across execution table rows
//! and extension op table rows.
//!
//! ## Key operations and their costs
//!
//! | Instruction              | Exec rows | Ext op rows |
//! |--------------------------|-----------|-------------|
//! | `mul_base_ext(c, a)`     | 1         | 1           |
//! | `add_ext(a, b)`          | 1         | 1           |
//! | `mul_ext(a, b)`          | 1         | 1           |
//! | `sub_ext(a, b)`          | 5         | 0           |
//! | `neg_ext(a)`             | 5         | 0           |
//! | `copy_ext(src, dst)`     | 5         | 0           |
//! | `dot_product_be(N)`      | 1         | N           |
//! | `dot_product_ee(N)`      | 1         | N           |
//! | `add_ee(N)`              | 1         | N           |
//!
//! Batched operations (`dot_product_be/ee(N)`, `add_ee(N)`) require operands to be in
//! **contiguous memory**. Making operands contiguous may require `copy_ext` (5 exec rows each)
//! or evaluating with a `dest` parameter (free if the top-level op supports it).

use std::collections::{BTreeMap, HashMap};

// ============================================================================
// Core IR: expression graph (independent of SymbolicExpression)
// ============================================================================

/// A node in the expression DAG.
#[derive(Clone, Debug)]
pub enum ExprNode {
    /// Column variable at a given index (contiguous in `inner_evals`).
    Variable(usize),
    /// Base-field constant (canonical u32).
    Constant(u32),
    /// Binary operation on two sub-expressions.
    BinOp { op: BinOpKind, lhs: ExprId, rhs: ExprId },
    /// Unary negation.
    Neg(ExprId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
}

/// Index into the expression arena.
pub type ExprId = usize;

/// The full expression DAG (shared sub-expressions represented by shared ExprIds).
#[derive(Clone, Debug)]
pub struct ExprGraph {
    pub nodes: Vec<ExprNode>,
    /// Reference count per node (how many parents + how many constraints reference it).
    pub ref_counts: Vec<usize>,
    /// The constraint expressions (indices into `nodes`).
    pub constraints: Vec<ExprId>,
    /// Bus flag expression.
    pub bus_flag: ExprId,
    /// Bus data expressions.
    pub bus_data: Vec<ExprId>,
}

// ============================================================================
// Instruction IR: what we emit
// ============================================================================

/// A single emitted instruction with a known cost.
#[derive(Clone, Debug)]
pub enum Instruction {
    /// `result = c * a` (base × extension). 1 exec + 1 ext op.
    MulBaseExt {
        base_const: u32,
        ext_operand: Operand,
        result: ResultSlot,
    },
    /// `result = a + b` (extension + extension). 1 exec + 1 ext op.
    AddExt { a: Operand, b: Operand, result: ResultSlot },
    /// `result = a * b` (extension × extension). 1 exec + 1 ext op.
    MulExt { a: Operand, b: Operand, result: ResultSlot },
    /// `result = a + c` (extension + base constant). 1 exec + 1 ext op.
    AddBaseExt {
        base_const: u32,
        ext_operand: Operand,
        result: ResultSlot,
    },
    /// `result = c - a` (base constant - extension). 5 exec + 0 ext op.
    SubBaseExt {
        base_const: u32,
        ext_operand: Operand,
        result: ResultSlot,
    },
    /// `result = a - c` (extension - base constant). 5 exec + 0 ext op.
    SubExtBase {
        ext_operand: Operand,
        base_const: u32,
        result: ResultSlot,
    },
    /// `result = a - b`. 5 exec + 0 ext op.
    SubExt { a: Operand, b: Operand, result: ResultSlot },
    /// `result = -a`. 5 exec + 0 ext op.
    NegExt { a: Operand, result: ResultSlot },
    /// `dest = src`. 5 exec + 0 ext op.
    CopyExt { src: Operand, dest: ResultSlot },
    /// `result = sum_{i=0}^{N-1} base_consts[i] * ext_operands[i]`. 1 exec + N ext op.
    DotProductBE {
        base_consts: Vec<u32>,
        ext_operands: Vec<Operand>,
        result: ResultSlot,
    },
    /// `result = sum_{i=0}^{N-1} a[i] * b[i]`. 1 exec + N ext op.
    DotProductEE {
        a_operands: Vec<Operand>,
        b_operands: Vec<Operand>,
        result: ResultSlot,
    },
    /// `result = sum_{i=0}^{N-1} (a[i] + b[i])`. 1 exec + N ext op.
    AddEE {
        a_operands: Vec<Operand>,
        b_operands: Vec<Operand>,
        result: ResultSlot,
    },
    /// Embed a base-field constant into extension field. ~5 exec + 0 ext op.
    EmbedConst { value: u32, result: ResultSlot },
}

/// Where an operand comes from.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Operand {
    /// A column variable: `inner_evals + DIM * index`.
    Variable(usize),
    /// Result of a previous instruction, identified by instruction index.
    InstructionResult(usize),
    /// A slot in a named contiguous buffer: `buffer_name[slot_index]`.
    BufferSlot { buffer: usize, slot: usize },
}

/// Where a result goes.
#[derive(Clone, Debug)]
pub enum ResultSlot {
    /// Fresh allocation (the instruction allocates its own output).
    Fresh(usize), // instruction index used as unique id
    /// Write into a named buffer slot.
    Buffer { buffer: usize, slot: usize },
}

// ============================================================================
// Solution: a complete instruction sequence with cost
// ============================================================================

/// A complete code generation solution.
#[derive(Clone, Debug)]
pub struct Solution {
    /// Contiguous buffers to allocate. Each entry is (name_suffix, n_elements).
    pub buffers: Vec<(String, usize)>,
    /// Base-field constant arrays. Key = contents, allocated once.
    pub const_arrays: BTreeMap<Vec<u32>, String>,
    /// The instruction sequence.
    pub instructions: Vec<Instruction>,
    /// Maps ExprId → which instruction produces it (for sharing/caching).
    pub expr_to_instruction: HashMap<ExprId, usize>,
}

/// Cost breakdown for a solution.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cost {
    pub exec_rows: usize,
    pub ext_op_rows: usize,
}

impl Cost {
    pub fn new(exec: usize, ext_op: usize) -> Self {
        Self {
            exec_rows: exec,
            ext_op_rows: ext_op,
        }
    }

    /// Weighted total cost. Both tables matter; extension op rows are ~1.5x more expensive
    /// per row (30 columns vs 20 columns), but execution table is larger.
    /// This weight can be tuned based on actual bottleneck analysis.
    pub fn weighted_total(&self) -> f64 {
        self.exec_rows as f64 + 1.5 * self.ext_op_rows as f64
    }
}

impl std::ops::Add for Cost {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Cost {
            exec_rows: self.exec_rows + rhs.exec_rows,
            ext_op_rows: self.ext_op_rows + rhs.ext_op_rows,
        }
    }
}

impl std::ops::AddAssign for Cost {
    fn add_assign(&mut self, rhs: Self) {
        self.exec_rows += rhs.exec_rows;
        self.ext_op_rows += rhs.ext_op_rows;
    }
}

// ============================================================================
// Cost computation
// ============================================================================

impl Instruction {
    /// Exact cost of this instruction.
    pub fn cost(&self) -> Cost {
        match self {
            Instruction::MulBaseExt { .. } => Cost::new(1, 1),
            Instruction::AddExt { .. } => Cost::new(1, 1),
            Instruction::MulExt { .. } => Cost::new(1, 1),
            Instruction::AddBaseExt { .. } => Cost::new(1, 1),
            Instruction::SubBaseExt { .. } => Cost::new(5, 0),
            Instruction::SubExtBase { .. } => Cost::new(5, 0),
            Instruction::SubExt { .. } => Cost::new(5, 0),
            Instruction::NegExt { .. } => Cost::new(5, 0),
            Instruction::CopyExt { .. } => Cost::new(5, 0),
            Instruction::EmbedConst { .. } => Cost::new(5, 0),
            Instruction::DotProductBE { base_consts, .. } => Cost::new(1, base_consts.len()),
            Instruction::DotProductEE { a_operands, .. } => Cost::new(1, a_operands.len()),
            Instruction::AddEE { a_operands, .. } => Cost::new(1, a_operands.len()),
        }
    }
}

/// Compute the total cost of a solution.
pub fn rate_solution(solution: &Solution) -> Cost {
    let mut total = Cost::default();

    // Cost of allocating and filling constant arrays (each element write is ~1 exec row).
    for consts in solution.const_arrays.keys() {
        total.exec_rows += consts.len();
    }

    // Cost of all instructions.
    for instr in &solution.instructions {
        total += instr.cost();
    }

    total
}

// ============================================================================
// Trivial solver: evaluate the expression tree naively (no batching)
// ============================================================================

/// Generate a trivial (non-optimized) solution: evaluate each expression node individually
/// using scalar operations. No dot_product, no add_ee, no contiguous buffers.
pub fn solve_trivial(graph: &ExprGraph) -> Solution {
    let mut solution = Solution {
        buffers: Vec::new(),
        const_arrays: BTreeMap::new(),
        instructions: Vec::new(),
        expr_to_instruction: HashMap::new(),
    };

    // Evaluate all constraint expressions, bus flag, and bus data.
    let mut all_roots: Vec<ExprId> = graph.constraints.clone();
    all_roots.push(graph.bus_flag);
    all_roots.extend(graph.bus_data.iter());

    for &root in &all_roots {
        eval_trivial(root, graph, &mut solution);
    }

    solution
}

/// Recursively evaluate a single expression, emitting scalar instructions.
/// Returns the instruction index that produces this expression's value.
fn eval_trivial(expr: ExprId, graph: &ExprGraph, solution: &mut Solution) -> usize {
    // Check if already evaluated (shared sub-expression).
    if let Some(&instr_idx) = solution.expr_to_instruction.get(&expr) {
        return instr_idx;
    }

    let idx = match &graph.nodes[expr] {
        ExprNode::Variable(_) => {
            // Variables don't need an instruction — they're referenced directly.
            // But we still record them so the cache works.
            let _instr_idx = solution.instructions.len();
            // No instruction emitted; we'll handle Variable references in Operand.
            // Just return a sentinel.
            return record_variable(expr, solution);
        }
        ExprNode::Constant(c) => {
            let instr_idx = solution.instructions.len();
            solution.instructions.push(Instruction::EmbedConst {
                value: *c,
                result: ResultSlot::Fresh(instr_idx),
            });
            instr_idx
        }
        ExprNode::Neg(inner) => {
            let inner_idx = eval_trivial(*inner, graph, solution);
            let instr_idx = solution.instructions.len();
            solution.instructions.push(Instruction::NegExt {
                a: operand_for(inner_idx, *inner, graph, solution),
                result: ResultSlot::Fresh(instr_idx),
            });
            instr_idx
        }
        ExprNode::BinOp { op, lhs, rhs } => {
            let lhs_val = *lhs;
            let rhs_val = *rhs;
            let op_val = *op;

            let c_lhs = match graph.nodes[lhs_val] {
                ExprNode::Constant(c) => Some(c),
                _ => None,
            };
            let c_rhs = match graph.nodes[rhs_val] {
                ExprNode::Constant(c) => Some(c),
                _ => None,
            };

            // Helper: evaluate both children, then push one instruction.
            // Always compute instr_idx RIGHT BEFORE push (children may grow the vec).
            match (c_lhs, c_rhs) {
                // Const * Ext or Ext * Const — inline constant, no embed_in_ef.
                (Some(c), None) if op_val == BinOpKind::Mul => {
                    let ri = eval_trivial(rhs_val, graph, solution);
                    let ro = operand_for(ri, rhs_val, graph, solution);
                    let ii = solution.instructions.len();
                    solution.instructions.push(Instruction::MulBaseExt {
                        base_const: c,
                        ext_operand: ro,
                        result: ResultSlot::Fresh(ii),
                    });
                    ii
                }
                (None, Some(c)) if op_val == BinOpKind::Mul => {
                    let li = eval_trivial(lhs_val, graph, solution);
                    let lo = operand_for(li, lhs_val, graph, solution);
                    let ii = solution.instructions.len();
                    solution.instructions.push(Instruction::MulBaseExt {
                        base_const: c,
                        ext_operand: lo,
                        result: ResultSlot::Fresh(ii),
                    });
                    ii
                }
                // All other cases: evaluate both children, then emit the operation.
                _ => {
                    let li = eval_trivial(lhs_val, graph, solution);
                    let ri = eval_trivial(rhs_val, graph, solution);
                    let lo = operand_for(li, lhs_val, graph, solution);
                    let ro = operand_for(ri, rhs_val, graph, solution);
                    let ii = solution.instructions.len();
                    match op_val {
                        BinOpKind::Add => solution.instructions.push(Instruction::AddExt {
                            a: lo,
                            b: ro,
                            result: ResultSlot::Fresh(ii),
                        }),
                        BinOpKind::Sub => solution.instructions.push(Instruction::SubExt {
                            a: lo,
                            b: ro,
                            result: ResultSlot::Fresh(ii),
                        }),
                        BinOpKind::Mul => solution.instructions.push(Instruction::MulExt {
                            a: lo,
                            b: ro,
                            result: ResultSlot::Fresh(ii),
                        }),
                    }
                    ii
                }
            }
        }
    };

    solution.expr_to_instruction.insert(expr, idx);
    idx
}

/// Record a variable in the solution without emitting an instruction.
fn record_variable(expr: ExprId, solution: &mut Solution) -> usize {
    // Use a sentinel: instruction index = usize::MAX means "it's a variable, use Operand::Variable".
    let sentinel = usize::MAX;
    solution.expr_to_instruction.insert(expr, sentinel);
    sentinel
}

/// Build an Operand for a previously evaluated expression.
fn operand_for(instr_idx: usize, expr: ExprId, graph: &ExprGraph, _solution: &Solution) -> Operand {
    if instr_idx == usize::MAX {
        // It's a variable.
        match graph.nodes[expr] {
            ExprNode::Variable(idx) => Operand::Variable(idx),
            _ => unreachable!("sentinel used for non-variable"),
        }
    } else {
        Operand::InstructionResult(instr_idx)
    }
}

// ============================================================================
// Smart solver: uses dot_product_be, add_ee, inline base-field constants
// ============================================================================

/// Optimized solver that:
/// 1. Inlines base-field constants into add/sub (no embed_in_ef for const+ext or ext-const)
/// 2. Detects sums of `Const*Var` products → dot_product_be when Variables are consecutive
/// 3. Detects sums of `Ext*Ext` products → dot_product_ee when non-shared
/// 4. Reuses constant arrays across calls (via const_arrays map)
pub fn solve_optimized(graph: &ExprGraph) -> Solution {
    let mut ctx = OptCtx {
        graph,
        solution: Solution {
            buffers: Vec::new(),
            const_arrays: BTreeMap::new(),
            instructions: Vec::new(),
            expr_to_instruction: HashMap::new(),
        },
    };

    let mut all_roots: Vec<ExprId> = graph.constraints.clone();
    all_roots.push(graph.bus_flag);
    all_roots.extend(graph.bus_data.iter());

    for &root in &all_roots {
        ctx.eval(root);
    }

    ctx.solution
}

struct OptCtx<'a> {
    graph: &'a ExprGraph,
    solution: Solution,
}

/// A term in a flattened sum: coefficient (sign) × expression.
#[derive(Clone)]
struct SumTerm {
    expr: ExprId,
    negated: bool,
}

/// A classified product in a sum.
enum ProductKind {
    /// base_const * ext_expr (ext_expr is NOT a constant)
    BE { base_const: u32, ext_expr: ExprId },
    /// ext_a * ext_b (neither is a constant)
    EE { a: ExprId, b: ExprId },
}

impl<'a> OptCtx<'a> {
    fn eval(&mut self, expr: ExprId) -> usize {
        if let Some(&idx) = self.solution.expr_to_instruction.get(&expr) {
            return idx;
        }

        let idx = match self.graph.nodes[expr].clone() {
            ExprNode::Variable(_) => return self.record_variable(expr),
            ExprNode::Constant(c) => self.push(Instruction::EmbedConst {
                value: c,
                result: ResultSlot::Fresh(0), // placeholder
            }),
            ExprNode::Neg(inner) => {
                let inner_idx = self.eval(inner);
                let op = self.operand(inner_idx, inner);
                self.push(Instruction::NegExt {
                    a: op,
                    result: ResultSlot::Fresh(0),
                })
            }
            ExprNode::BinOp { op, lhs, rhs } => self.eval_binop(op, lhs, rhs, expr),
        };

        self.solution.expr_to_instruction.insert(expr, idx);
        idx
    }

    fn eval_binop(&mut self, op: BinOpKind, lhs: ExprId, rhs: ExprId, self_expr: ExprId) -> usize {
        let c_lhs = self.get_const(lhs);
        let c_rhs = self.get_const(rhs);

        match (c_lhs, c_rhs, op) {
            // Const * Ext → MulBaseExt (no embed)
            (Some(c), None, BinOpKind::Mul) => {
                let ri = self.eval(rhs);
                let ro = self.operand(ri, rhs);
                self.push(Instruction::MulBaseExt {
                    base_const: c,
                    ext_operand: ro,
                    result: ResultSlot::Fresh(0),
                })
            }
            (None, Some(c), BinOpKind::Mul) => {
                let li = self.eval(lhs);
                let lo = self.operand(li, lhs);
                self.push(Instruction::MulBaseExt {
                    base_const: c,
                    ext_operand: lo,
                    result: ResultSlot::Fresh(0),
                })
            }
            // Const + Ext → AddBaseExt (no embed)
            (Some(c), None, BinOpKind::Add) => {
                let ri = self.eval(rhs);
                let ro = self.operand(ri, rhs);
                self.push(Instruction::AddBaseExt {
                    base_const: c,
                    ext_operand: ro,
                    result: ResultSlot::Fresh(0),
                })
            }
            (None, Some(c), BinOpKind::Add) => {
                let li = self.eval(lhs);
                let lo = self.operand(li, lhs);
                self.push(Instruction::AddBaseExt {
                    base_const: c,
                    ext_operand: lo,
                    result: ResultSlot::Fresh(0),
                })
            }
            // Const - Ext → SubBaseExt
            (Some(c), None, BinOpKind::Sub) => {
                let ri = self.eval(rhs);
                let ro = self.operand(ri, rhs);
                self.push(Instruction::SubBaseExt {
                    base_const: c,
                    ext_operand: ro,
                    result: ResultSlot::Fresh(0),
                })
            }
            // Ext - Const → SubExtBase
            (None, Some(c), BinOpKind::Sub) => {
                let li = self.eval(lhs);
                let lo = self.operand(li, lhs);
                self.push(Instruction::SubExtBase {
                    ext_operand: lo,
                    base_const: c,
                    result: ResultSlot::Fresh(0),
                })
            }
            // Ext + Ext or Ext - Ext: try to batch sums of products
            (None, None, BinOpKind::Add | BinOpKind::Sub) => {
                if let Some(idx) = self.try_dot_product(self_expr) {
                    return idx;
                }
                // Fallback: scalar
                let li = self.eval(lhs);
                let ri = self.eval(rhs);
                let lo = self.operand(li, lhs);
                let ro = self.operand(ri, rhs);
                let instr = if op == BinOpKind::Add {
                    Instruction::AddExt {
                        a: lo,
                        b: ro,
                        result: ResultSlot::Fresh(0),
                    }
                } else {
                    Instruction::SubExt {
                        a: lo,
                        b: ro,
                        result: ResultSlot::Fresh(0),
                    }
                };
                self.push(instr)
            }
            // Ext * Ext
            (None, None, BinOpKind::Mul) => {
                let li = self.eval(lhs);
                let ri = self.eval(rhs);
                let lo = self.operand(li, lhs);
                let ro = self.operand(ri, rhs);
                self.push(Instruction::MulExt {
                    a: lo,
                    b: ro,
                    result: ResultSlot::Fresh(0),
                })
            }
            // Both constants (rare — symbolic already folds)
            (Some(_), Some(_), _) => {
                let li = self.eval(lhs);
                let ri = self.eval(rhs);
                let lo = self.operand(li, lhs);
                let ro = self.operand(ri, rhs);
                let instr = match op {
                    BinOpKind::Add => Instruction::AddExt {
                        a: lo,
                        b: ro,
                        result: ResultSlot::Fresh(0),
                    },
                    BinOpKind::Sub => Instruction::SubExt {
                        a: lo,
                        b: ro,
                        result: ResultSlot::Fresh(0),
                    },
                    BinOpKind::Mul => Instruction::MulExt {
                        a: lo,
                        b: ro,
                        result: ResultSlot::Fresh(0),
                    },
                };
                self.push(instr)
            }
        }
    }

    /// Try to batch a sum of products into dot_product_be or dot_product_ee.
    fn try_dot_product(&mut self, expr: ExprId) -> Option<usize> {
        // Flatten the addition chain, stopping at shared/cached nodes.
        let mut terms = Vec::new();
        self.flatten_sum(expr, false, &mut terms);
        if terms.len() < 3 {
            return None;
        }

        // Classify each term.
        let mut be_pos: Vec<(u32, ExprId)> = Vec::new(); // (const, ext_expr)
        let mut be_neg: Vec<(u32, ExprId)> = Vec::new();
        let mut ee_pos: Vec<(ExprId, ExprId)> = Vec::new();
        let mut ee_neg: Vec<(ExprId, ExprId)> = Vec::new();
        let mut remainders: Vec<SumTerm> = Vec::new();

        for term in &terms {
            if let Some(pk) = self.classify_as_product(term.expr) {
                match pk {
                    ProductKind::BE { base_const, ext_expr } => {
                        if term.negated { &mut be_neg } else { &mut be_pos }.push((base_const, ext_expr));
                    }
                    ProductKind::EE { a, b } => {
                        if term.negated { &mut ee_neg } else { &mut ee_pos }.push((a, b));
                    }
                }
            } else {
                remainders.push(term.clone());
            }
        }

        let n_be = be_pos.len() + be_neg.len();
        let n_ee = ee_pos.len() + ee_neg.len();

        // Check if batching is cost-effective.
        // dot_product(N) costs 1 exec + N ext_op vs N*(1 exec + 1 ext_op) + (N-1)*(1 exec + 1 ext_op) = 2N-1 each.
        // So savings = (2N-2) exec + (N-1) ext_op minus any copy cost.
        // Copies: 5 exec each. Break-even: 1 + 5*copies < 2N-1 → copies < (2N-2)/5.
        // For consecutive Variables: 0 copies. Always worth it for N >= 2.
        let be_worth = n_be >= 3 && {
            let copies = self.count_be_copies(&be_pos) + self.count_be_copies(&be_neg);
            5 * copies + 1 < 2 * n_be // conservative: must save exec rows
        };
        let ee_worth = n_ee >= 3 && {
            let copies = self.count_ee_copies(&ee_pos) + self.count_ee_copies(&ee_neg);
            5 * copies + 1 < 2 * n_ee
        };

        if !be_worth && !ee_worth {
            return None;
        }

        // Emit batched operations. Store (Operand, negated) pairs.
        let mut parts: Vec<(Operand, bool)> = Vec::new();

        if be_worth {
            if !be_pos.is_empty() {
                let idx = self.emit_dot_product_be(&be_pos);
                parts.push((Operand::InstructionResult(idx), false));
            }
            if !be_neg.is_empty() {
                let idx = self.emit_dot_product_be(&be_neg);
                parts.push((Operand::InstructionResult(idx), true));
            }
        } else {
            for (c, ext) in be_pos {
                let ei = self.eval(ext);
                let eo = self.operand(ei, ext);
                let idx = self.push(Instruction::MulBaseExt {
                    base_const: c,
                    ext_operand: eo,
                    result: ResultSlot::Fresh(0),
                });
                parts.push((Operand::InstructionResult(idx), false));
            }
            for (c, ext) in be_neg {
                let ei = self.eval(ext);
                let eo = self.operand(ei, ext);
                let idx = self.push(Instruction::MulBaseExt {
                    base_const: c,
                    ext_operand: eo,
                    result: ResultSlot::Fresh(0),
                });
                parts.push((Operand::InstructionResult(idx), true));
            }
        }

        if ee_worth {
            if !ee_pos.is_empty() {
                let idx = self.emit_dot_product_ee(&ee_pos);
                parts.push((Operand::InstructionResult(idx), false));
            }
            if !ee_neg.is_empty() {
                let idx = self.emit_dot_product_ee(&ee_neg);
                parts.push((Operand::InstructionResult(idx), true));
            }
        } else {
            for (a, b) in ee_pos {
                let ai = self.eval(a);
                let bi = self.eval(b);
                let ao = self.operand(ai, a);
                let bo = self.operand(bi, b);
                let idx = self.push(Instruction::MulExt {
                    a: ao,
                    b: bo,
                    result: ResultSlot::Fresh(0),
                });
                parts.push((Operand::InstructionResult(idx), false));
            }
            for (a, b) in ee_neg {
                let ai = self.eval(a);
                let bi = self.eval(b);
                let ao = self.operand(ai, a);
                let bo = self.operand(bi, b);
                let idx = self.push(Instruction::MulExt {
                    a: ao,
                    b: bo,
                    result: ResultSlot::Fresh(0),
                });
                parts.push((Operand::InstructionResult(idx), true));
            }
        }

        // Evaluate remainders.
        for term in &remainders {
            let idx = self.eval(term.expr);
            let op = self.operand(idx, term.expr);
            parts.push((op, term.negated));
        }

        // Combine all parts.
        Some(self.combine_parts(&parts))
    }

    fn emit_dot_product_be(&mut self, products: &[(u32, ExprId)]) -> usize {
        let consts: Vec<u32> = products.iter().map(|(c, _)| *c).collect();
        let mut operands = Vec::new();
        for &(_, ext) in products {
            let ei = self.eval(ext);
            operands.push(self.operand(ei, ext));
        }

        // Check for consecutive Variables (zero-copy fast path).
        let consecutive_start = self.check_consecutive_vars(&operands);
        if let Some(start) = consecutive_start {
            // Use inner_evals pointer directly.
            let op_list = (0..products.len()).map(|i| Operand::Variable(start + i)).collect();
            self.push(Instruction::DotProductBE {
                base_consts: consts,
                ext_operands: op_list,
                result: ResultSlot::Fresh(0),
            })
        } else {
            self.push(Instruction::DotProductBE {
                base_consts: consts,
                ext_operands: operands,
                result: ResultSlot::Fresh(0),
            })
        }
    }

    fn emit_dot_product_ee(&mut self, products: &[(ExprId, ExprId)]) -> usize {
        let mut a_ops = Vec::new();
        let mut b_ops = Vec::new();
        for &(a, b) in products {
            let ai = self.eval(a);
            let bi = self.eval(b);
            a_ops.push(self.operand(ai, a));
            b_ops.push(self.operand(bi, b));
        }
        self.push(Instruction::DotProductEE {
            a_operands: a_ops,
            b_operands: b_ops,
            result: ResultSlot::Fresh(0),
        })
    }

    fn combine_parts(&mut self, parts: &[(Operand, bool)]) -> usize {
        assert!(!parts.is_empty());
        let (ref first_op, first_neg) = parts[0];
        let mut acc_op = if first_neg {
            let idx = self.push(Instruction::NegExt {
                a: first_op.clone(),
                result: ResultSlot::Fresh(0),
            });
            Operand::InstructionResult(idx)
        } else {
            first_op.clone()
        };

        for (cur_op, negated) in &parts[1..] {
            let idx = if *negated {
                self.push(Instruction::SubExt {
                    a: acc_op,
                    b: cur_op.clone(),
                    result: ResultSlot::Fresh(0),
                })
            } else {
                self.push(Instruction::AddExt {
                    a: acc_op,
                    b: cur_op.clone(),
                    result: ResultSlot::Fresh(0),
                })
            };
            acc_op = Operand::InstructionResult(idx);
        }
        match acc_op {
            Operand::InstructionResult(idx) => idx,
            _ => self.push(Instruction::CopyExt {
                src: acc_op,
                dest: ResultSlot::Fresh(0),
            }),
        }
    }

    // --- Helpers ---

    fn flatten_sum(&self, expr: ExprId, negated: bool, terms: &mut Vec<SumTerm>) {
        // Don't expand shared (ref_count > 1) or already-evaluated nodes.
        if self.graph.ref_counts[expr] > 1 || self.solution.expr_to_instruction.contains_key(&expr) {
            terms.push(SumTerm { expr, negated });
            return;
        }
        match &self.graph.nodes[expr] {
            ExprNode::BinOp {
                op: BinOpKind::Add,
                lhs,
                rhs,
            } => {
                self.flatten_sum(*lhs, negated, terms);
                self.flatten_sum(*rhs, negated, terms);
            }
            ExprNode::BinOp {
                op: BinOpKind::Sub,
                lhs,
                rhs,
            } => {
                self.flatten_sum(*lhs, negated, terms);
                self.flatten_sum(*rhs, !negated, terms);
            }
            ExprNode::Neg(inner) => {
                self.flatten_sum(*inner, !negated, terms);
            }
            _ => terms.push(SumTerm { expr, negated }),
        }
    }

    fn classify_as_product(&self, expr: ExprId) -> Option<ProductKind> {
        // Only classify non-shared, non-evaluated Mul nodes.
        if self.graph.ref_counts[expr] > 1 || self.solution.expr_to_instruction.contains_key(&expr) {
            return None;
        }
        match &self.graph.nodes[expr] {
            ExprNode::BinOp {
                op: BinOpKind::Mul,
                lhs,
                rhs,
            } => {
                let cl = self.get_const(*lhs);
                let cr = self.get_const(*rhs);
                match (cl, cr) {
                    (Some(c), None) => Some(ProductKind::BE {
                        base_const: c,
                        ext_expr: *rhs,
                    }),
                    (None, Some(c)) => Some(ProductKind::BE {
                        base_const: c,
                        ext_expr: *lhs,
                    }),
                    (None, None) => Some(ProductKind::EE { a: *lhs, b: *rhs }),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn count_be_copies(&self, products: &[(u32, ExprId)]) -> usize {
        // If all ext operands are consecutive Variables → 0 copies.
        if self.are_consecutive_vars(products.iter().map(|(_, e)| *e)) {
            return 0;
        }
        products.iter().filter(|(_, e)| self.needs_copy(*e)).count()
    }

    fn count_ee_copies(&self, products: &[(ExprId, ExprId)]) -> usize {
        products
            .iter()
            .map(|(a, b)| (if self.needs_copy(*a) { 1 } else { 0 }) + (if self.needs_copy(*b) { 1 } else { 0 }))
            .sum()
    }

    fn needs_copy(&self, expr: ExprId) -> bool {
        matches!(self.graph.nodes[expr], ExprNode::Variable(_) | ExprNode::Constant(_))
            || self.solution.expr_to_instruction.contains_key(&expr)
    }

    fn are_consecutive_vars(&self, exprs: impl Iterator<Item = ExprId>) -> bool {
        let mut prev: Option<usize> = None;
        for e in exprs {
            match self.graph.nodes[e] {
                ExprNode::Variable(idx) => {
                    if let Some(p) = prev {
                        if idx != p + 1 {
                            return false;
                        }
                    }
                    prev = Some(idx);
                }
                _ => return false,
            }
        }
        prev.is_some()
    }

    fn check_consecutive_vars(&self, operands: &[Operand]) -> Option<usize> {
        let mut prev: Option<usize> = None;
        for op in operands {
            match op {
                Operand::Variable(idx) => {
                    if let Some(p) = prev {
                        if *idx != p + 1 {
                            return None;
                        }
                    }
                    prev = Some(*idx);
                }
                _ => return None,
            }
        }
        operands.first().and_then(|op| match op {
            Operand::Variable(idx) => Some(*idx),
            _ => None,
        })
    }

    fn get_const(&self, expr: ExprId) -> Option<u32> {
        match self.graph.nodes[expr] {
            ExprNode::Constant(c) => Some(c),
            _ => None,
        }
    }

    fn push(&mut self, mut instr: Instruction) -> usize {
        let idx = self.solution.instructions.len();
        // Fix up the placeholder ResultSlot.
        match &mut instr {
            Instruction::MulBaseExt { result, .. }
            | Instruction::AddBaseExt { result, .. }
            | Instruction::SubBaseExt { result, .. }
            | Instruction::SubExtBase { result, .. }
            | Instruction::AddExt { result, .. }
            | Instruction::MulExt { result, .. }
            | Instruction::SubExt { result, .. }
            | Instruction::NegExt { result, .. }
            | Instruction::CopyExt { dest: result, .. }
            | Instruction::EmbedConst { result, .. }
            | Instruction::DotProductBE { result, .. }
            | Instruction::DotProductEE { result, .. }
            | Instruction::AddEE { result, .. } => {
                *result = ResultSlot::Fresh(idx);
            }
        }
        self.solution.instructions.push(instr);
        idx
    }

    fn record_variable(&mut self, expr: ExprId) -> usize {
        let sentinel = usize::MAX;
        self.solution.expr_to_instruction.insert(expr, sentinel);
        sentinel
    }

    fn operand(&self, instr_idx: usize, expr: ExprId) -> Operand {
        if instr_idx == usize::MAX {
            match self.graph.nodes[expr] {
                ExprNode::Variable(idx) => Operand::Variable(idx),
                _ => unreachable!(),
            }
        } else {
            Operand::InstructionResult(instr_idx)
        }
    }

    fn operand_from_instr(&self, instr_idx: usize) -> Operand {
        Operand::InstructionResult(instr_idx)
    }
}

// ============================================================================
// Conversion from SymbolicExpression to ExprGraph
// ============================================================================

use backend::*;
use lean_vm::*;

/// Convert the symbolic constraint expressions from an AIR table into an ExprGraph.
pub fn expr_graph_from_symbolic<T: TableT>(table: &T) -> ExprGraph
where
    T::ExtraData: Default,
{
    let (constraints, bus_flag, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(table);

    let mut nodes = Vec::new();
    let mut arena_to_expr: HashMap<u32, ExprId> = HashMap::new();

    let constraint_ids: Vec<ExprId> = constraints
        .iter()
        .map(|c| convert_symbolic(*c, &mut nodes, &mut arena_to_expr))
        .collect();
    let bus_flag_id = convert_symbolic(bus_flag, &mut nodes, &mut arena_to_expr);
    let bus_data_ids: Vec<ExprId> = bus_data
        .iter()
        .map(|d| convert_symbolic(*d, &mut nodes, &mut arena_to_expr))
        .collect();

    // Compute reference counts.
    let mut ref_counts = vec![0usize; nodes.len()];
    for &root in constraint_ids
        .iter()
        .chain(std::iter::once(&bus_flag_id))
        .chain(bus_data_ids.iter())
    {
        count_expr_refs(root, &nodes, &mut ref_counts);
    }

    ExprGraph {
        nodes,
        ref_counts,
        constraints: constraint_ids,
        bus_flag: bus_flag_id,
        bus_data: bus_data_ids,
    }
}

fn convert_symbolic(
    expr: SymbolicExpression<F>,
    nodes: &mut Vec<ExprNode>,
    arena_map: &mut HashMap<u32, ExprId>,
) -> ExprId {
    match expr {
        SymbolicExpression::Variable(v) => {
            let id = nodes.len();
            nodes.push(ExprNode::Variable(v.index));
            id
        }
        SymbolicExpression::Constant(c) => {
            let id = nodes.len();
            nodes.push(ExprNode::Constant(c.as_canonical_u32()));
            id
        }
        SymbolicExpression::Operation(idx) => {
            if let Some(&existing) = arena_map.get(&idx) {
                return existing;
            }
            let node = get_node::<F>(idx);
            match node.op {
                SymbolicOperation::Neg => {
                    let inner = convert_symbolic(node.lhs, nodes, arena_map);
                    let id = nodes.len();
                    nodes.push(ExprNode::Neg(inner));
                    arena_map.insert(idx, id);
                    id
                }
                _ => {
                    let lhs = convert_symbolic(node.lhs, nodes, arena_map);
                    let rhs = convert_symbolic(node.rhs, nodes, arena_map);
                    let op = match node.op {
                        SymbolicOperation::Add => BinOpKind::Add,
                        SymbolicOperation::Sub => BinOpKind::Sub,
                        SymbolicOperation::Mul => BinOpKind::Mul,
                        SymbolicOperation::Neg => unreachable!(),
                    };
                    let id = nodes.len();
                    nodes.push(ExprNode::BinOp { op, lhs, rhs });
                    arena_map.insert(idx, id);
                    id
                }
            }
        }
    }
}

fn count_expr_refs(expr: ExprId, nodes: &[ExprNode], counts: &mut [usize]) {
    counts[expr] += 1;
    if counts[expr] > 1 {
        return; // Already counted children.
    }
    match &nodes[expr] {
        ExprNode::Variable(_) | ExprNode::Constant(_) => {}
        ExprNode::Neg(inner) => count_expr_refs(*inner, nodes, counts),
        ExprNode::BinOp { lhs, rhs, .. } => {
            count_expr_refs(*lhs, nodes, counts);
            count_expr_refs(*rhs, nodes, counts);
        }
    }
}

// ============================================================================
// Solution → zkDSL code emission
// ============================================================================

const INNER_VALUES_VAR: &str = "inner_evals";

/// Convert a Solution into zkDSL code for one AIR table.
/// `table_index` is the table number (0, 1, 2).
/// `n_constraints` is the number of constraint expressions.
/// `n_bus_data` is the number of bus data expressions.
pub fn solution_to_zkdsl(solution: &Solution, graph: &ExprGraph, table_index: usize) -> String {
    let n_constraints = graph.constraints.len();
    let n_bus_data = graph.bus_data.len();

    let mut res = format!(
        "def evaluate_air_constraints_table_{}({}, air_alpha_powers, bus_beta, logup_alphas_eq_poly):\n",
        table_index, INNER_VALUES_VAR
    );

    res += &format!("\n    constraints_buf = Array(DIM * {})", n_constraints);

    // Build dest map: instruction_idx → dest string.
    // If an instruction ONLY produces a constraint/bus_data result (not used by other instructions),
    // we can write directly to the target buffer slot (no copy needed).
    let mut instr_dest: HashMap<usize, String> = HashMap::new();
    let mut instr_use_count: HashMap<usize, usize> = HashMap::new();

    // Count how many times each instruction result is used as an operand by other instructions.
    for instr in &solution.instructions {
        for op in instr_operands(instr) {
            if let Operand::InstructionResult(idx) = op {
                *instr_use_count.entry(*idx).or_insert(0) += 1;
            }
        }
    }

    // Assign dests for constraint expressions whose producing instruction is not used elsewhere.
    for (ci, &expr_id) in graph.constraints.iter().enumerate() {
        if let Some(&instr_idx) = solution.expr_to_instruction.get(&expr_id) {
            if instr_idx != usize::MAX && *instr_use_count.get(&instr_idx).unwrap_or(&0) == 0 {
                if instruction_supports_dest(&solution.instructions[instr_idx]) {
                    instr_dest.insert(instr_idx, format!("constraints_buf + {} * DIM", ci));
                }
            }
        }
    }

    // Emit all instructions.
    let mut var_names: HashMap<usize, String> = HashMap::new();
    let mut ctr = 0usize;

    for (i, instr) in solution.instructions.iter().enumerate() {
        let dest = instr_dest.get(&i).map(|s| s.as_str());
        let name = emit_instruction_with_dest(instr, dest, &var_names, &mut res, &mut ctr);
        var_names.insert(i, name);
    }

    // Write constraint results that couldn't use dest (shared expressions).
    for (ci, &expr_id) in graph.constraints.iter().enumerate() {
        if let Some(&instr_idx) = solution.expr_to_instruction.get(&expr_id) {
            if !instr_dest.contains_key(&instr_idx) {
                let src = resolve_operand_name(&operand_for_result(instr_idx, expr_id, graph), &var_names);
                res += &format!("\n    copy_5({}, constraints_buf + {} * DIM)", src, ci);
            }
        }
    }

    // Bus data.
    let flag_expr = graph.bus_flag;
    let flag_name = if let Some(&instr_idx) = solution.expr_to_instruction.get(&flag_expr) {
        resolve_operand_name(&operand_for_result(instr_idx, flag_expr, graph), &var_names)
    } else {
        format!("{} + DIM * 0", INNER_VALUES_VAR)
    };

    res += &format!("\n    buff = Array(DIM * {})", n_bus_data);
    for (i, &data_expr) in graph.bus_data.iter().enumerate() {
        if let Some(&instr_idx) = solution.expr_to_instruction.get(&data_expr) {
            let src = resolve_operand_name(&operand_for_result(instr_idx, data_expr, graph), &var_names);
            res += &format!("\n    copy_5({}, buff + DIM * {})", src, i);
        }
    }

    // Standard bus + constraint weighting (same for all tables).
    res += "\n    bus_res_init = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee(buff, logup_alphas_eq_poly, bus_res_init, {})",
        n_bus_data
    );
    res += &format!(
        "\n    bus_res: Mut = add_extension_ret(mul_base_extension_ret(LOGUP_PRECOMPILE_DOMAINSEP, logup_alphas_eq_poly + {} * DIM), bus_res_init)",
        max_bus_width_including_domainsep().next_power_of_two() - 1
    );
    res += "\n    bus_res = mul_extension_ret(bus_res, bus_beta)";
    res += &format!("\n    sum: Mut = add_extension_ret(bus_res, {})", flag_name);
    res += "\n    weighted_constraints = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee(air_alpha_powers + DIM, constraints_buf, weighted_constraints, {})",
        n_constraints
    );
    res += "\n    sum = add_extension_ret(sum, weighted_constraints)";
    res += "\n    return sum";
    res += "\n";
    res
}

fn operand_for_result(instr_idx: usize, expr_id: ExprId, graph: &ExprGraph) -> Operand {
    if instr_idx == usize::MAX {
        match graph.nodes[expr_id] {
            ExprNode::Variable(idx) => Operand::Variable(idx),
            _ => Operand::InstructionResult(instr_idx),
        }
    } else {
        Operand::InstructionResult(instr_idx)
    }
}

fn resolve_operand_name(op: &Operand, var_names: &HashMap<usize, String>) -> String {
    match op {
        Operand::Variable(idx) => format!("{} + DIM * {}", INNER_VALUES_VAR, idx),
        Operand::InstructionResult(idx) => var_names
            .get(idx)
            .cloned()
            .unwrap_or_else(|| format!("MISSING_{}", idx)),
        Operand::BufferSlot { buffer, slot } => format!("buf_{} + DIM * {}", buffer, slot),
    }
}

/// Check if an instruction can write directly to a dest buffer.
fn instruction_supports_dest(instr: &Instruction) -> bool {
    matches!(
        instr,
        Instruction::AddExt { .. }
            | Instruction::MulExt { .. }
            | Instruction::SubExt { .. }
            | Instruction::MulBaseExt { .. }
            | Instruction::AddBaseExt { .. }
            | Instruction::DotProductBE { .. }
            | Instruction::DotProductEE { .. }
            | Instruction::AddEE { .. }
    )
}

/// Extract all operands from an instruction (for use-count analysis).
fn instr_operands(instr: &Instruction) -> Vec<&Operand> {
    match instr {
        Instruction::MulBaseExt { ext_operand, .. }
        | Instruction::AddBaseExt { ext_operand, .. }
        | Instruction::SubBaseExt { ext_operand, .. }
        | Instruction::SubExtBase { ext_operand, .. } => vec![ext_operand],
        Instruction::AddExt { a, b, .. } | Instruction::MulExt { a, b, .. } | Instruction::SubExt { a, b, .. } => {
            vec![a, b]
        }
        Instruction::NegExt { a, .. } => vec![a],
        Instruction::CopyExt { src, .. } => vec![src],
        Instruction::EmbedConst { .. } => vec![],
        Instruction::DotProductBE { ext_operands, .. } => ext_operands.iter().collect(),
        Instruction::DotProductEE {
            a_operands, b_operands, ..
        } => a_operands.iter().chain(b_operands.iter()).collect(),
        Instruction::AddEE {
            a_operands, b_operands, ..
        } => a_operands.iter().chain(b_operands.iter()).collect(),
    }
}

/// Emit an instruction, optionally writing to a dest buffer instead of a fresh var.
fn emit_instruction_with_dest(
    instr: &Instruction,
    dest: Option<&str>,
    var_names: &HashMap<usize, String>,
    res: &mut String,
    ctr: &mut usize,
) -> String {
    // If dest is provided and the instruction supports it, use the dest variant.
    if let Some(d) = dest {
        match instr {
            Instruction::AddExt { a, b, .. } => {
                let an = resolve_operand_name(a, var_names);
                let bn = resolve_operand_name(b, var_names);
                res.push_str(&format!("\n    add_ee({}, {}, {})", an, bn, d));
                return d.to_string();
            }
            Instruction::MulExt { a, b, .. } => {
                let an = resolve_operand_name(a, var_names);
                let bn = resolve_operand_name(b, var_names);
                res.push_str(&format!("\n    mul_extension({}, {}, {})", an, bn, d));
                return d.to_string();
            }
            Instruction::SubExt { a, b, .. } => {
                let an = resolve_operand_name(a, var_names);
                let bn = resolve_operand_name(b, var_names);
                res.push_str(&format!("\n    sub_extension({}, {}, {})", an, bn, d));
                return d.to_string();
            }
            Instruction::MulBaseExt {
                base_const,
                ext_operand,
                ..
            } => {
                let ext = resolve_operand_name(ext_operand, var_names);
                let tmp = format!("aux_{}", *ctr);
                *ctr += 1;
                res.push_str(&format!(
                    "\n    {} = Array(1)\n    {}[0] = {}\n    dot_product_be({}, {}, {})",
                    tmp, tmp, base_const, tmp, ext, d
                ));
                return d.to_string();
            }
            Instruction::AddBaseExt {
                base_const,
                ext_operand,
                ..
            } => {
                let ext = resolve_operand_name(ext_operand, var_names);
                let tmp = format!("aux_{}", *ctr);
                *ctr += 1;
                res.push_str(&format!(
                    "\n    {} = Array(1)\n    {}[0] = {}\n    add_be({}, {}, {})",
                    tmp, tmp, base_const, tmp, ext, d
                ));
                return d.to_string();
            }
            _ => {} // Fall through to normal emission + copy
        }
    }

    // Normal emission (no dest or unsupported).
    let name = emit_instruction(instr, var_names, res, ctr);

    // If dest was requested but the instruction didn't support it, copy.
    if let Some(d) = dest {
        res.push_str(&format!("\n    copy_5({}, {})", name, d));
        return d.to_string();
    }

    name
}

fn emit_instruction(
    instr: &Instruction,
    var_names: &HashMap<usize, String>,
    res: &mut String,
    ctr: &mut usize,
) -> String {
    let mut next_var = || {
        let name = format!("aux_{}", *ctr);
        *ctr += 1;
        name
    };

    match instr {
        Instruction::EmbedConst { value, .. } => {
            let v = next_var();
            res.push_str(&format!("\n    {} = embed_in_ef({})", v, value));
            v
        }
        Instruction::MulBaseExt {
            base_const,
            ext_operand,
            ..
        } => {
            let ext = resolve_operand_name(ext_operand, var_names);
            let v = next_var();
            res.push_str(&format!(
                "\n    {} = mul_base_extension_ret({}, {})",
                v, base_const, ext
            ));
            v
        }
        Instruction::AddExt { a, b, .. } => {
            let an = resolve_operand_name(a, var_names);
            let bn = resolve_operand_name(b, var_names);
            let v = next_var();
            res.push_str(&format!("\n    {} = add_extension_ret({}, {})", v, an, bn));
            v
        }
        Instruction::MulExt { a, b, .. } => {
            let an = resolve_operand_name(a, var_names);
            let bn = resolve_operand_name(b, var_names);
            let v = next_var();
            res.push_str(&format!("\n    {} = mul_extension_ret({}, {})", v, an, bn));
            v
        }
        Instruction::AddBaseExt {
            base_const,
            ext_operand,
            ..
        } => {
            let ext = resolve_operand_name(ext_operand, var_names);
            let v = next_var();
            res.push_str(&format!(
                "\n    {} = add_base_extension_ret({}, {})",
                v, base_const, ext
            ));
            v
        }
        Instruction::SubBaseExt {
            base_const,
            ext_operand,
            ..
        } => {
            let ext = resolve_operand_name(ext_operand, var_names);
            let v = next_var();
            res.push_str(&format!(
                "\n    {} = sub_base_extension_ret({}, {})",
                v, base_const, ext
            ));
            v
        }
        Instruction::SubExtBase {
            ext_operand,
            base_const,
            ..
        } => {
            let ext = resolve_operand_name(ext_operand, var_names);
            let v = next_var();
            res.push_str(&format!(
                "\n    {} = sub_extension_base_ret({}, {})",
                v, ext, base_const
            ));
            v
        }
        Instruction::SubExt { a, b, .. } => {
            let an = resolve_operand_name(a, var_names);
            let bn = resolve_operand_name(b, var_names);
            let v = next_var();
            res.push_str(&format!("\n    {} = sub_extension_ret({}, {})", v, an, bn));
            v
        }
        Instruction::NegExt { a, .. } => {
            let an = resolve_operand_name(a, var_names);
            let v = next_var();
            res.push_str(&format!("\n    {} = opposite_extension_ret({})", v, an));
            v
        }
        Instruction::CopyExt { src, dest } => {
            let sn = resolve_operand_name(src, var_names);
            let dn = match dest {
                ResultSlot::Fresh(_) => {
                    let v = next_var();
                    res.push_str(&format!("\n    {} = Array(DIM)", v));
                    v
                }
                ResultSlot::Buffer { buffer, slot } => format!("buf_{} + DIM * {}", buffer, slot),
            };
            res.push_str(&format!("\n    copy_5({}, {})", sn, dn));
            dn
        }
        Instruction::DotProductBE {
            base_consts,
            ext_operands,
            ..
        } => {
            // Emit constant buffer.
            let cb = next_var();
            res.push_str(&format!("\n    {} = Array({})", cb, base_consts.len()));
            for (i, c) in base_consts.iter().enumerate() {
                res.push_str(&format!("\n    {}[{}] = {}", cb, i, c));
            }
            // Emit ext buffer.
            let eb = next_var();
            let n = ext_operands.len();
            res.push_str(&format!("\n    {} = Array(DIM * {})", eb, n));
            for (i, op) in ext_operands.iter().enumerate() {
                let src = resolve_operand_name(op, var_names);
                res.push_str(&format!("\n    copy_5({}, {} + DIM * {})", src, eb, i));
            }
            let v = next_var();
            res.push_str(&format!("\n    {} = Array(DIM)", v));
            res.push_str(&format!("\n    dot_product_be({}, {}, {}, {})", cb, eb, v, n));
            v
        }
        Instruction::DotProductEE {
            a_operands, b_operands, ..
        } => {
            let n = a_operands.len();
            let ab = next_var();
            res.push_str(&format!("\n    {} = Array(DIM * {})", ab, n));
            for (i, op) in a_operands.iter().enumerate() {
                let s = resolve_operand_name(op, var_names);
                res.push_str(&format!("\n    copy_5({}, {} + DIM * {})", s, ab, i));
            }
            let bb = next_var();
            res.push_str(&format!("\n    {} = Array(DIM * {})", bb, n));
            for (i, op) in b_operands.iter().enumerate() {
                let s = resolve_operand_name(op, var_names);
                res.push_str(&format!("\n    copy_5({}, {} + DIM * {})", s, bb, i));
            }
            let v = next_var();
            res.push_str(&format!("\n    {} = Array(DIM)", v));
            res.push_str(&format!("\n    dot_product_ee({}, {}, {}, {})", ab, bb, v, n));
            v
        }
        Instruction::AddEE {
            a_operands, b_operands, ..
        } => {
            let n = a_operands.len();
            let ab = next_var();
            res.push_str(&format!("\n    {} = Array(DIM * {})", ab, n));
            for (i, op) in a_operands.iter().enumerate() {
                let s = resolve_operand_name(op, var_names);
                res.push_str(&format!("\n    copy_5({}, {} + DIM * {})", s, ab, i));
            }
            let bb = next_var();
            res.push_str(&format!("\n    {} = Array(DIM * {})", bb, n));
            for (i, op) in b_operands.iter().enumerate() {
                let s = resolve_operand_name(op, var_names);
                res.push_str(&format!("\n    copy_5({}, {} + DIM * {})", s, bb, i));
            }
            let v = next_var();
            res.push_str(&format!("\n    {} = Array(DIM)", v));
            res.push_str(&format!("\n    add_ee({}, {}, {}, {})", ab, bb, v, n));
            v
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: build a simple expression graph for testing.
    fn make_weighted_sum_graph() -> ExprGraph {
        // Expression: 2*x0 + 3*x1 + 1*x2 + 1*x3
        // (models one output of apply_mat4)
        let mut nodes = Vec::new();

        // Variables (consecutive indices 0-3)
        let x0 = 0;
        nodes.push(ExprNode::Variable(0)); // node 0
        let x1 = 1;
        nodes.push(ExprNode::Variable(1)); // node 1
        let x2 = 2;
        nodes.push(ExprNode::Variable(2)); // node 2
        let x3 = 3;
        nodes.push(ExprNode::Variable(3)); // node 3

        // Constants
        let c2 = 4;
        nodes.push(ExprNode::Constant(2)); // node 4
        let c3 = 5;
        nodes.push(ExprNode::Constant(3)); // node 5
        let c1a = 6;
        nodes.push(ExprNode::Constant(1)); // node 6
        let c1b = 7;
        nodes.push(ExprNode::Constant(1)); // node 7

        // Products: 2*x0, 3*x1, 1*x2, 1*x3
        let p0 = 8;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Mul,
            lhs: c2,
            rhs: x0,
        });
        let p1 = 9;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Mul,
            lhs: c3,
            rhs: x1,
        });
        let p2 = 10;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Mul,
            lhs: c1a,
            rhs: x2,
        });
        let p3 = 11;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Mul,
            lhs: c1b,
            rhs: x3,
        });

        // Sum: ((p0 + p1) + p2) + p3
        let s01 = 12;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Add,
            lhs: p0,
            rhs: p1,
        });
        let s012 = 13;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Add,
            lhs: s01,
            rhs: p2,
        });
        let s0123 = 14;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Add,
            lhs: s012,
            rhs: p3,
        });

        let n = nodes.len();
        let ref_counts = vec![1; n]; // simplified

        ExprGraph {
            nodes,
            ref_counts,
            constraints: vec![s0123],
            bus_flag: x0, // dummy
            bus_data: vec![],
        }
    }

    #[test]
    fn test_trivial_solver_cost() {
        let graph = make_weighted_sum_graph();
        let solution = solve_trivial(&graph);
        let cost = rate_solution(&solution);

        // Expected trivial cost for 2*x0 + 3*x1 + 1*x2 + 1*x3:
        // 4 MulBaseExt (4 exec + 4 ext op) — constants inlined, no embed_in_ef
        // 3 AddExt (3 exec + 3 ext op)
        // Total: 7 exec + 7 ext op
        assert_eq!(cost.exec_rows, 7, "exec rows");
        assert_eq!(cost.ext_op_rows, 7, "ext op rows");

        println!("Trivial solution cost: {cost:?}");
        println!("Weighted total: {:.1}", cost.weighted_total());
        println!("Instructions: {}", solution.instructions.len());
    }

    #[test]
    fn test_optimal_would_be_dot_product() {
        // The optimal solution for 2*x0 + 3*x1 + 1*x2 + 1*x3
        // where x0..x3 are consecutive Variables:
        // 1 dot_product_be([2,3,1,1], inner_evals+0, result, 4) = 1 exec + 4 ext op
        // Constants [2,3,1,1] written once = 4 exec rows

        let optimal_cost = Cost::new(1 + 4, 4); // 5 exec, 4 ext op
        let graph = make_weighted_sum_graph();
        let trivial = rate_solution(&solve_trivial(&graph));

        println!("Trivial:  {trivial:?} (weighted: {:.1})", trivial.weighted_total());
        println!(
            "Optimal:  {optimal_cost:?} (weighted: {:.1})",
            optimal_cost.weighted_total()
        );
        println!(
            "Savings:  {} exec rows, {} ext op rows",
            trivial.exec_rows - optimal_cost.exec_rows,
            trivial.ext_op_rows - optimal_cost.ext_op_rows
        );

        assert!(optimal_cost.weighted_total() < trivial.weighted_total());
    }

    #[test]
    fn test_shared_subexpression() {
        // Expression: (a * b) + (a * b) where a*b is shared (ref_count = 2).
        // Trivial: 1 MulExt + 1 AddExt = 2 exec + 2 ext op.
        // (The shared a*b is only evaluated once.)
        let mut nodes = Vec::new();
        let a = 0;
        nodes.push(ExprNode::Variable(0));
        let b = 1;
        nodes.push(ExprNode::Variable(1));
        let ab = 2;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Mul,
            lhs: a,
            rhs: b,
        });
        let sum = 3;
        nodes.push(ExprNode::BinOp {
            op: BinOpKind::Add,
            lhs: ab,
            rhs: ab, // shared!
        });

        let mut ref_counts = vec![0; 4];
        ref_counts[ab] = 2;
        ref_counts[sum] = 1;
        ref_counts[a] = 1;
        ref_counts[b] = 1;

        let graph = ExprGraph {
            nodes,
            ref_counts,
            constraints: vec![sum],
            bus_flag: a,
            bus_data: vec![],
        };

        let solution = solve_trivial(&graph);
        let cost = rate_solution(&solution);

        // Should be: 1 MulExt(a, b) + 1 AddExt(ab, ab) = 2 exec + 2 ext op
        assert_eq!(cost.exec_rows, 2);
        assert_eq!(cost.ext_op_rows, 2);
    }

    #[test]
    fn test_rate_solution_with_copies() {
        // Manually construct a solution that uses copies to make operands contiguous,
        // then uses dot_product_be.
        let solution = Solution {
            buffers: vec![("ext_buf".to_string(), 4)],
            const_arrays: BTreeMap::from([(vec![2, 3, 1, 1], "mds_0".to_string())]),
            instructions: vec![
                // 4 copies into buffer (4 * 5 exec = 20 exec)
                Instruction::CopyExt {
                    src: Operand::Variable(0),
                    dest: ResultSlot::Buffer { buffer: 0, slot: 0 },
                },
                Instruction::CopyExt {
                    src: Operand::Variable(1),
                    dest: ResultSlot::Buffer { buffer: 0, slot: 1 },
                },
                Instruction::CopyExt {
                    src: Operand::Variable(2),
                    dest: ResultSlot::Buffer { buffer: 0, slot: 2 },
                },
                Instruction::CopyExt {
                    src: Operand::Variable(3),
                    dest: ResultSlot::Buffer { buffer: 0, slot: 3 },
                },
                // 1 dot_product_be(4): 1 exec + 4 ext op
                Instruction::DotProductBE {
                    base_consts: vec![2, 3, 1, 1],
                    ext_operands: vec![
                        Operand::BufferSlot { buffer: 0, slot: 0 },
                        Operand::BufferSlot { buffer: 0, slot: 1 },
                        Operand::BufferSlot { buffer: 0, slot: 2 },
                        Operand::BufferSlot { buffer: 0, slot: 3 },
                    ],
                    result: ResultSlot::Fresh(4),
                },
            ],
            expr_to_instruction: HashMap::new(),
        };

        let cost = rate_solution(&solution);
        // 4 const writes + 4*5 copies + 1 dp_be = 4 + 20 + 1 = 25 exec, 4 ext op
        assert_eq!(cost.exec_rows, 25);
        assert_eq!(cost.ext_op_rows, 4);

        // Compare: trivial is 7 exec + 7 ext op.
        // With copies, dot_product is WORSE on exec (25 > 7) but better on ext op (4 < 7).
        // This demonstrates why copies are expensive and contiguous buffers matter.
        println!("With copies: {cost:?} (weighted: {:.1})", cost.weighted_total());

        // Now the zero-copy version (Variables already contiguous):
        let zero_copy_solution = Solution {
            buffers: vec![],
            const_arrays: BTreeMap::from([(vec![2, 3, 1, 1], "mds_0".to_string())]),
            instructions: vec![Instruction::DotProductBE {
                base_consts: vec![2, 3, 1, 1],
                ext_operands: vec![
                    Operand::Variable(0),
                    Operand::Variable(1),
                    Operand::Variable(2),
                    Operand::Variable(3),
                ],
                result: ResultSlot::Fresh(0),
            }],
            expr_to_instruction: HashMap::new(),
        };

        let zc_cost = rate_solution(&zero_copy_solution);
        // 4 const writes + 1 dp_be = 5 exec, 4 ext op
        assert_eq!(zc_cost.exec_rows, 5);
        assert_eq!(zc_cost.ext_op_rows, 4);
        println!("Zero-copy:   {zc_cost:?} (weighted: {:.1})", zc_cost.weighted_total());
    }
}
