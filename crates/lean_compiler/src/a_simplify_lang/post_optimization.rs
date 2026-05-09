use std::collections::{BTreeMap, BTreeSet, btree_map::Entry};
use std::ops::Bound;

use backend::PrimeCharacteristicRing;

use crate::{F, a_simplify_lang::*, lang::ConstExpression};

pub fn propagate_copies(program: &mut SimpleProgram) {
    for func in program.functions.values_mut() {
        // Pass 1: copy propagation. `var = mem_expr + 0` with `var`
        // single-defined ⇒ rewrite uses with `mem_expr`, drop the assignment.
        let refs = get_var_refs(&func.instructions);
        let mut subst = BTreeMap::<Var, SimpleExpr>::new();
        build_substitutions(&func.instructions, &refs, &mut subst);
        if !subst.is_empty() {
            apply_substitutions(&mut func.instructions, &subst);
        }

        // Pass 2: fold `v_inner = K + base; v_ptr = arr + v_inner; res = m[v_ptr + 0]`
        // into `v_ptr = arr + base; res = m[v_ptr + K]`.
        let refs = get_var_refs(&func.instructions);
        fold_const_offset_into_deref(&mut func.instructions, &refs);

        // Pass 3: Dedup Add/Mul/Sub/Div with same operands
        let refs = get_var_refs(&func.instructions);
        dedup_arithmetic_operations(&mut func.instructions, &refs);

        // Pass 4: Fuse `v = m[ptr+s]; assert v == x` ⇒ `x = m[ptr+s]`.
        let refs = get_var_refs(&func.instructions);
        fuse_raw_asserts(&mut func.instructions, &refs);

        // Pass 5: fuse `Assignment + AssertEq`('c = 0`and 'c = a * b` => `0 = a * b`).
        let refs = get_var_refs(&func.instructions);
        fuse_assign_asserts(&mut func.instructions, &refs);
    }
}

#[derive(Default, Clone, Copy)]
struct VarRefs {
    definitions: u32,
    uses: u32,
}

fn get_var_refs(lines: &[SimpleLine]) -> BTreeMap<Var, VarRefs> {
    fn walk(lines: &[SimpleLine], counts: &mut BTreeMap<Var, VarRefs>) {
        for line in lines {
            match line {
                SimpleLine::Assignment {
                    var: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
                    ..
                }
                | SimpleLine::HintMAlloc { var: v, .. }
                | SimpleLine::ConstMalloc { var: v, .. }
                | SimpleLine::RawAccess {
                    res: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
                    ..
                } => counts.entry(v.clone()).or_default().definitions += 1,
                SimpleLine::FunctionCall { return_data, .. } => {
                    for v in return_data {
                        counts.entry(v.clone()).or_default().definitions += 1;
                    }
                }
                _ => {}
            }
            // Reads only (skip `RawAccess.res`)
            let reads: Vec<&SimpleExpr> = match line {
                SimpleLine::RawAccess { index, .. } => vec![index],
                _ => line.operand_exprs(),
            };
            for e in reads {
                if let Some(v) = e.as_var() {
                    counts.entry(v.clone()).or_default().uses += 1;
                }
            }
            for block in line.nested_blocks() {
                walk(block, counts);
            }
        }
    }
    let mut counts = BTreeMap::new();
    walk(lines, &mut counts);
    counts
}

fn build_substitutions(lines: &[SimpleLine], refs: &BTreeMap<Var, VarRefs>, subst: &mut BTreeMap<Var, SimpleExpr>) {
    for line in lines {
        if let SimpleLine::Assignment {
            var: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
            op: MathOperation::Add,
            arg0: arg0 @ SimpleExpr::Memory(_),
            arg1: SimpleExpr::Constant(c),
        } = line
            && c.naive_eval() == Some(F::ZERO)
            && refs.get(v).map(|r| r.definitions) == Some(1)
        {
            subst.insert(v.clone(), chase(arg0.clone(), subst));
            continue;
        }
        for block in line.nested_blocks() {
            build_substitutions(block, refs, subst);
        }
    }
}

fn chase(mut expr: SimpleExpr, subst: &BTreeMap<Var, SimpleExpr>) -> SimpleExpr {
    while let Some(v) = expr.as_var()
        && let Some(t) = subst.get(v)
    {
        expr = t.clone();
    }
    expr
}

fn apply_substitutions(lines: &mut Vec<SimpleLine>, subst: &BTreeMap<Var, SimpleExpr>) {
    for line in lines.iter_mut() {
        for expr in line.operand_exprs_mut() {
            if let Some(v) = expr.as_var()
                && let Some(replacement) = subst.get(v)
            {
                *expr = replacement.clone();
            }
        }
        for block in line.nested_blocks_mut() {
            apply_substitutions(block, subst);
        }
    }
    lines.retain(|line| match line {
        SimpleLine::Assignment {
            var: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
            ..
        }
        | SimpleLine::ForwardDeclaration { var: v } => !subst.contains_key(v),
        _ => true,
    });
}

#[derive(Default)]
struct Fusions {
    replacements: BTreeMap<usize, SimpleLine>,
    lines_to_drop: BTreeSet<usize>,
    declarations_to_drop: BTreeSet<Var>,
}

/// Index of `AssertEq` line positions keyed by each variable that appears as a side.
/// Lookups are O(log N) and a "claim" removes the entry from both vars' sets so it
/// can never be picked twice — making fusion passes O(N log N) overall.
#[derive(Default)]
struct AssertIndex {
    by_var: BTreeMap<Var, BTreeSet<usize>>,
}

impl AssertIndex {
    fn build(lines: &[SimpleLine]) -> Self {
        let mut by_var: BTreeMap<Var, BTreeSet<usize>> = BTreeMap::new();
        for (j, line) in lines.iter().enumerate() {
            let SimpleLine::AssertEq { left, right, .. } = line else {
                continue;
            };
            if let Some(v) = left.as_var() {
                by_var.entry(v.clone()).or_default().insert(j);
            }
            if let Some(v) = right.as_var() {
                by_var.entry(v.clone()).or_default().insert(j);
            }
        }
        Self { by_var }
    }

    /// Find the first unclaimed AssertEq line at index > i where `v` appears as a side,
    /// claim it (removing j from both vars' sets), and return (j, other_side).
    fn pop_first_after<'a>(&mut self, lines: &'a [SimpleLine], i: usize, v: &Var) -> Option<(usize, &'a SimpleExpr)> {
        let j = self
            .by_var
            .get(v)?
            .range((Bound::Excluded(i), Bound::Unbounded))
            .next()
            .copied()?;

        let SimpleLine::AssertEq { left, right, .. } = &lines[j] else {
            unreachable!()
        };
        let lv = left.as_var().cloned();
        let rv = right.as_var().cloned();

        if let Some(lv) = lv.as_ref()
            && let Some(set) = self.by_var.get_mut(lv)
        {
            set.remove(&j);
        }
        if let Some(rv) = rv.as_ref()
            && lv.as_ref() != Some(rv)
            && let Some(set) = self.by_var.get_mut(rv)
        {
            set.remove(&j);
        }

        let other = match (left.as_var(), right.as_var()) {
            (Some(n), _) if n == v => right,
            (_, Some(n)) if n == v => left,
            _ => unreachable!(),
        };
        Some((j, other))
    }
}

fn is_one_time_var(v: &Var, refs: &BTreeMap<Var, VarRefs>) -> bool {
    let r: VarRefs = refs.get(v).copied().unwrap_or_default();
    r.definitions == 1 && r.uses == 1
}

fn is_uniquely_defined(v: &Var, refs: &BTreeMap<Var, VarRefs>) -> bool {
    refs.get(v).map(|r| r.definitions) == Some(1)
}

fn apply_fusions(lines: &mut Vec<SimpleLine>, fusions: Fusions) {
    for (j, new_line) in fusions.replacements {
        lines[j] = new_line;
    }
    let mut idx = 0;
    lines.retain(|_| {
        let keep = !fusions.lines_to_drop.contains(&idx);
        idx += 1;
        keep
    });
    lines.retain(
        |line| !matches!(line, SimpleLine::ForwardDeclaration { var } if fusions.declarations_to_drop.contains(var)),
    );
}

fn fuse_raw_asserts(lines: &mut Vec<SimpleLine>, refs: &BTreeMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            fuse_raw_asserts(block, refs);
        }
    }

    let mut assert_index = AssertIndex::build(lines);
    let mut fusions = Fusions::default();
    for i in 0..lines.len() {
        let SimpleLine::RawAccess { res, index, shift } = &lines[i] else {
            continue;
        };
        let Some(v) = res.as_var() else { continue };
        if !is_one_time_var(v, refs) {
            continue;
        }
        let v_clone = v.clone();
        if let Some((j, other)) = assert_index.pop_first_after(lines, i, &v_clone) {
            let new_line = SimpleLine::RawAccess {
                res: other.clone(),
                index: index.clone(),
                shift: shift.clone(),
            };
            fusions.lines_to_drop.insert(i);
            fusions.declarations_to_drop.insert(v_clone);
            fusions.replacements.insert(j, new_line);
        }
    }
    apply_fusions(lines, fusions);
}

fn fuse_assign_asserts(lines: &mut Vec<SimpleLine>, refs: &BTreeMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            fuse_assign_asserts(block, refs);
        }
    }

    let mut assert_index = AssertIndex::build(lines);
    let mut fusions = Fusions::default();
    for i in 0..lines.len() {
        let SimpleLine::Assignment { var, op, arg0, arg1 } = &lines[i] else {
            continue;
        };
        let Some(v) = var.as_var() else { continue };
        if !is_one_time_var(v, refs) {
            continue;
        }
        let v_clone = v.clone();
        let op = *op;
        let arg0 = arg0.clone();
        let arg1 = arg1.clone();
        if let Some((j, other)) = assert_index.pop_first_after(lines, i, &v_clone) {
            let new_line = SimpleLine::Assignment {
                var: other.clone(),
                op,
                arg0,
                arg1,
            };
            fusions.lines_to_drop.insert(i);
            fusions.declarations_to_drop.insert(v_clone);
            fusions.replacements.insert(j, new_line);
        }
    }
    apply_fusions(lines, fusions);
}

/// The simplifier lowers `arr[base + K]` (runtime `base`, compile-time const `K`)
/// to three lines: compute `K + base`, add `arr`, then DEREF with shift = 0. But DEREF
/// already takes a constant shift, so we can absorb K there and skip the inner add:
///
///   v_inner = K + base                       v_ptr = arr + base
///   v_ptr   = arr + v_inner            ==>   res   = memory[v_ptr + K]
///   res     = memory[v_ptr + 0]
///
/// Soundness: `v_inner` and `v_ptr` must each be uniquely defined and uniquely used
fn fold_const_offset_into_deref(lines: &mut Vec<SimpleLine>, refs: &BTreeMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            fold_const_offset_into_deref(block, refs);
        }
    }

    // Map each uniquely-defined Add var to its line index.
    let def_index: BTreeMap<Var, usize> = lines
        .iter()
        .enumerate()
        .filter_map(|(i, line)| match line {
            SimpleLine::Assignment {
                var: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
                op: MathOperation::Add,
                ..
            } if is_uniquely_defined(v, refs) => Some((v.clone(), i)),
            _ => None,
        })
        .collect();

    let one_use = |v: &Var| matches!(refs.get(v), Some(r) if r.definitions == 1 && r.uses == 1);

    // Phase 1: collect (raw_access_idx, v_ptr_def_idx, arg_pos, mem_part, K, v_inner_def_idx, v_inner_var).
    // (note the uses==1 on both v_ptr and v_inner)
    let mut work: Vec<(usize, usize, usize, SimpleExpr, ConstExpression, usize, Var)> = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let SimpleLine::RawAccess { index, shift, .. } = line else {
            continue;
        };
        if shift.naive_eval() != Some(F::ZERO) {
            continue;
        }
        let Some(v_ptr) = index.as_var() else { continue };
        if !one_use(v_ptr) {
            continue;
        }
        let Some(&v_ptr_idx) = def_index.get(v_ptr) else {
            continue;
        };
        let SimpleLine::Assignment {
            op: MathOperation::Add,
            arg0,
            arg1,
            ..
        } = &lines[v_ptr_idx]
        else {
            unreachable!();
        };

        for (pos, side) in [arg0, arg1].iter().enumerate() {
            let Some(v_inner) = side.as_var() else { continue };
            if !one_use(v_inner) {
                continue;
            }
            let Some(&inner_idx) = def_index.get(v_inner) else {
                continue;
            };
            let SimpleLine::Assignment {
                op: MathOperation::Add,
                arg0: a0,
                arg1: a1,
                ..
            } = &lines[inner_idx]
            else {
                unreachable!();
            };
            let (k, mem) = match (a0, a1) {
                (SimpleExpr::Constant(c), SimpleExpr::Memory(_)) => (c.clone(), a1.clone()),
                (SimpleExpr::Memory(_), SimpleExpr::Constant(c)) => (c.clone(), a0.clone()),
                _ => continue,
            };
            work.push((i, v_ptr_idx, pos, mem, k, inner_idx, v_inner.clone()));
            break;
        }
    }

    if work.is_empty() {
        return;
    }

    // Phase 2: apply rewrites and collect lines/declarations to drop.
    let mut to_drop = BTreeSet::<usize>::new();
    let mut decls_to_drop = BTreeSet::<Var>::new();
    for (raw_i, ptr_i, pos, mem, k, inner_i, var) in work {
        let SimpleLine::RawAccess { shift, .. } = &mut lines[raw_i] else {
            unreachable!();
        };
        *shift = k;
        let SimpleLine::Assignment { arg0, arg1, .. } = &mut lines[ptr_i] else {
            unreachable!();
        };
        if pos == 0 {
            *arg0 = mem;
        } else {
            *arg1 = mem;
        }
        to_drop.insert(inner_i);
        decls_to_drop.insert(var);
    }

    let mut idx = 0;
    lines.retain(|line| {
        let keep = !to_drop.contains(&idx)
            && !matches!(line, SimpleLine::ForwardDeclaration { var } if decls_to_drop.contains(var));
        idx += 1;
        keep
    });
}

/// CSE (Common Subexpression Elimination)
fn dedup_arithmetic_operations(lines: &mut Vec<SimpleLine>, refs: &BTreeMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            dedup_arithmetic_operations(block, refs);
        }
    }

    let mut first_def: BTreeMap<(MathOperation, SimpleExpr, SimpleExpr), Var> = BTreeMap::new();
    let mut subst: BTreeMap<Var, SimpleExpr> = BTreeMap::new();

    for line in lines.iter() {
        let SimpleLine::Assignment {
            var: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
            op,
            arg0,
            arg1,
        } = line
        else {
            continue;
        };
        if !op.supports_runtime() {
            continue;
        }
        if !is_uniquely_defined(v, refs) {
            continue;
        }
        let mut a = chase(arg0.clone(), &subst);
        let mut b = chase(arg1.clone(), &subst);
        if matches!(op, MathOperation::Add | MathOperation::Mul) && a > b {
            std::mem::swap(&mut a, &mut b);
        }

        match first_def.entry((*op, a, b)) {
            Entry::Occupied(e) => {
                subst.insert(
                    v.clone(),
                    SimpleExpr::Memory(VarOrConstMallocAccess::Var(e.get().clone())),
                );
            }
            Entry::Vacant(e) => {
                e.insert(v.clone());
            }
        }
    }

    if !subst.is_empty() {
        apply_substitutions(lines, &subst);
    }
}
