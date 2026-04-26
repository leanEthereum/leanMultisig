use std::collections::HashMap;

use backend::PrimeCharacteristicRing;

use crate::{F, a_simplify_lang::*};

pub fn propagate_copies(program: &mut SimpleProgram) {
    for func in program.functions.values_mut() {
        let counts = count_defs(&func.instructions);
        let mut subst = HashMap::<Var, SimpleExpr>::new();
        build_substitutions(&func.instructions, &counts, &mut subst);
        if !subst.is_empty() {
            apply_substitutions(&mut func.instructions, &subst);
        }
    }
}

fn count_defs(lines: &[SimpleLine]) -> HashMap<Var, usize> {
    fn walk(lines: &[SimpleLine], counts: &mut HashMap<Var, usize>) {
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
                } => *counts.entry(v.clone()).or_default() += 1,
                SimpleLine::FunctionCall { return_data, .. } => {
                    for v in return_data {
                        *counts.entry(v.clone()).or_default() += 1;
                    }
                }
                _ => {}
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

fn build_substitutions(lines: &[SimpleLine], counts: &HashMap<Var, usize>, subst: &mut HashMap<Var, SimpleExpr>) {
    for line in lines {
        if let SimpleLine::Assignment {
            var: VarOrConstMallocAccess::Var(v),
            operation: MathOperation::Add,
            arg0: arg0 @ SimpleExpr::Memory(_),
            arg1: SimpleExpr::Constant(c),
        } = line
            && c.naive_eval() == Some(F::ZERO)
            && counts.get(v).copied() == Some(1)
        {
            subst.insert(v.clone(), chase(arg0.clone(), subst));
            continue;
        }
        for block in line.nested_blocks() {
            build_substitutions(block, counts, subst);
        }
    }
}

fn chase(mut expr: SimpleExpr, subst: &HashMap<Var, SimpleExpr>) -> SimpleExpr {
    while let SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)) = &expr
        && let Some(t) = subst.get(v)
    {
        expr = t.clone();
    }
    expr
}

fn apply_substitutions(lines: &mut Vec<SimpleLine>, subst: &HashMap<Var, SimpleExpr>) {
    for line in lines.iter_mut() {
        for expr in line.operand_exprs_mut() {
            if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)) = expr
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
