use std::collections::{HashMap, HashSet};

use backend::PrimeCharacteristicRing;

use crate::{F, a_simplify_lang::*};

pub fn propagate_copies(program: &mut SimpleProgram) {
    for func in program.functions.values_mut() {
        let refs = get_var_refs(&func.instructions);

        // Pass 1: Add-equality copy propagation. `var = mem_expr + 0` with `var`
        // single-defined ⇒ rewrite uses with `mem_expr`, drop the assignment.
        let mut subst = HashMap::<Var, SimpleExpr>::new();
        build_substitutions(&func.instructions, &refs, &mut subst);
        if !subst.is_empty() {
            apply_substitutions(&mut func.instructions, &subst);
        }

        // Pass 2: RawAccess+AssertEq fusion. A var defined exactly once (by a
        // `RawAccess`) and referenced exactly once (in an `AssertEq`) ⇒ move
        // the AssertEq's other side into the `RawAccess`.
        fuse_raw_asserts(&mut func.instructions, &refs);
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
                    var: VarOrConstMallocAccess::Var(v),
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
            for e in line.operand_exprs() {
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
            var: VarOrConstMallocAccess::Var(v),
            operation: MathOperation::Add,
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
            var: VarOrConstMallocAccess::Var(v),
            ..
        }
        | SimpleLine::ForwardDeclaration { var: v } => !subst.contains_key(v),
        _ => true,
    });
}

fn fuse_raw_asserts(lines: &mut Vec<SimpleLine>, refs: &HashMap<Var, VarRefs>) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            fuse_raw_asserts(block, refs);
        }
    }

    let mut replacements = HashMap::<usize, SimpleLine>::new(); // j -> new RawAccess
    let mut drop_lines = HashSet::<usize>::new();
    let mut drop_decls = HashSet::<Var>::new();

    for i in 0..lines.len() {
        let SimpleLine::RawAccess {
            res: SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)),
            index,
            shift,
        } = &lines[i]
        else {
            continue;
        };
        // `uses == 2`: the RawAccess slot itself plus exactly one other
        // operand-position reference (which we look for in an AssertEq below).
        let r = refs.get(v).copied().unwrap_or_default();
        if r.definitions != 1 || r.uses != 2 {
            continue;
        }
        for (j, line) in lines.iter().enumerate().skip(i + 1) {
            if replacements.contains_key(&j) {
                // An AssertEq can be claimed by at most one RawAccess
                continue;
            }
            let SimpleLine::AssertEq { left, right, .. } = line else {
                continue;
            };
            let other = match (left.as_var(), right.as_var()) {
                (Some(n), _) if n == v => right.clone(),
                (_, Some(n)) if n == v => left.clone(),
                _ => continue,
            };
            replacements.insert(
                j,
                SimpleLine::RawAccess {
                    res: other,
                    index: index.clone(),
                    shift: shift.clone(),
                },
            );
            drop_lines.insert(i);
            drop_decls.insert(v.clone());
            break;
        }
    }

    for (j, new_line) in replacements {
        lines[j] = new_line;
    }
    // Drop the original RawAccess lines
    let mut idx = 0;
    lines.retain(|_| {
        let keep = !drop_lines.contains(&idx);
        idx += 1;
        keep
    });
    // Drop any ForwardDeclarations of vars we removed
    lines.retain(|line| !matches!(line, SimpleLine::ForwardDeclaration { var } if drop_decls.contains(var)));
}
