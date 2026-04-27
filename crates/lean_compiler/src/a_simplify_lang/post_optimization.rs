use std::collections::{HashMap, HashSet};

use backend::PrimeCharacteristicRing;

use crate::{F, a_simplify_lang::*};

pub fn propagate_copies(program: &mut SimpleProgram) {
    for func in program.functions.values_mut() {
        // Pass 1: copy propagation. `var = mem_expr + 0` with `var`
        // single-defined ⇒ rewrite uses with `mem_expr`, drop the assignment.
        let refs = get_var_refs(&func.instructions);
        let mut subst = HashMap::<Var, SimpleExpr>::new();
        build_substitutions(&func.instructions, &refs, &mut subst);
        if !subst.is_empty() {
            apply_substitutions(&mut func.instructions, &subst);
        }

        // Pass 2: fuse `RawAccess + AssertEq` into a single DEREF
        let refs = get_var_refs(&func.instructions);
        fuse_raw_asserts(&mut func.instructions, &refs);

        // Pass 3: fuse `Assignment + AssertEq`('c = 0`and 'c = a * b` => `0 = a * b`).
        let refs = get_var_refs(&func.instructions);
        fuse_assign_asserts(&mut func.instructions, &refs);
    }
}

#[derive(Default, Clone, Copy)]
struct VarRefs {
    definitions: u32,
    uses: u32,
}

fn get_var_refs(lines: &[SimpleLine]) -> HashMap<Var, VarRefs> {
    fn walk(lines: &[SimpleLine], counts: &mut HashMap<Var, VarRefs>) {
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
    let mut counts = HashMap::new();
    walk(lines, &mut counts);
    counts
}

fn build_substitutions(lines: &[SimpleLine], refs: &HashMap<Var, VarRefs>, subst: &mut HashMap<Var, SimpleExpr>) {
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

fn chase(mut expr: SimpleExpr, subst: &HashMap<Var, SimpleExpr>) -> SimpleExpr {
    while let Some(v) = expr.as_var()
        && let Some(t) = subst.get(v)
    {
        expr = t.clone();
    }
    expr
}

fn apply_substitutions(lines: &mut Vec<SimpleLine>, subst: &HashMap<Var, SimpleExpr>) {
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
    replacements: HashMap<usize, SimpleLine>,
    lines_to_drop: HashSet<usize>,
    declarations_to_drop: HashSet<Var>,
}

/// Search `lines[i+1..]` for an unclaimed `AssertEq` where `v` is one side.
/// Returns `(j, other_side)` if found.
fn find_fusable_assert<'a>(
    lines: &'a [SimpleLine],
    i: usize,
    v: &Var,
    fusions: &Fusions,
) -> Option<(usize, &'a SimpleExpr)> {
    for (j, line) in lines.iter().enumerate().skip(i + 1) {
        if fusions.replacements.contains_key(&j) {
            // An AssertEq can be claimed only once
            continue;
        }
        let SimpleLine::AssertEq { left, right, .. } = line else {
            continue;
        };
        match (left.as_var(), right.as_var()) {
            (Some(n), _) if n == v => return Some((j, right)),
            (_, Some(n)) if n == v => return Some((j, left)),
            _ => continue,
        }
    }
    None
}

fn is_one_time_var(v: &Var, refs: &HashMap<Var, VarRefs>) -> bool {
    let r: VarRefs = refs.get(v).copied().unwrap_or_default();
    r.definitions == 1 && r.uses == 1
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

fn fuse_raw_asserts(lines: &mut Vec<SimpleLine>, refs: &HashMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            fuse_raw_asserts(block, refs);
        }
    }

    let mut fusions = Fusions::default();
    for i in 0..lines.len() {
        let SimpleLine::RawAccess { res, index, shift } = &lines[i] else {
            continue;
        };
        let Some(v) = res.as_var() else { continue };
        if !is_one_time_var(v, refs) {
            continue;
        }
        if let Some((j, other)) = find_fusable_assert(lines, i, v, &fusions) {
            fusions.lines_to_drop.insert(i);
            fusions.declarations_to_drop.insert(v.clone());
            fusions.replacements.insert(
                j,
                SimpleLine::RawAccess {
                    res: other.clone(),
                    index: index.clone(),
                    shift: shift.clone(),
                },
            );
        }
    }
    apply_fusions(lines, fusions);
}

fn fuse_assign_asserts(lines: &mut Vec<SimpleLine>, refs: &HashMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            fuse_assign_asserts(block, refs);
        }
    }

    let mut fusions = Fusions::default();
    for i in 0..lines.len() {
        let SimpleLine::Assignment { var, op, arg0, arg1 } = &lines[i] else {
            continue;
        };
        let Some(v) = var.as_var() else { continue };
        if !is_one_time_var(v, refs) {
            continue;
        }
        if let Some((j, other)) = find_fusable_assert(lines, i, v, &fusions) {
            fusions.lines_to_drop.insert(i);
            fusions.declarations_to_drop.insert(v.clone());
            fusions.replacements.insert(
                j,
                SimpleLine::Assignment {
                    var: other.clone(),
                    op: *op,
                    arg0: arg0.clone(),
                    arg1: arg1.clone(),
                },
            );
        }
    }
    apply_fusions(lines, fusions);
}
