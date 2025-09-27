use crate::{ir::*, lang::*};
use std::collections::BTreeSet;

/// Finds all internal variables declared within a set of instructions.
///
/// This function recursively traverses all instruction types to discover
/// variables that need stack allocation.
pub fn find_internal_vars(lines: &[SimpleLine]) -> BTreeSet<Var> {
    let mut internal_vars = BTreeSet::new();

    for line in lines {
        match line {
            SimpleLine::Match(m) => {
                for arm in &m.arms {
                    internal_vars.extend(find_internal_vars(arm));
                }
            }
            SimpleLine::Assignment(a) => {
                if let VarOrConstMallocAccess::Var(var) = &a.var {
                    internal_vars.insert(var.clone());
                }
            }
            SimpleLine::DynamicAlloc(d) => {
                internal_vars.insert(d.var.clone());
            }
            SimpleLine::StaticAlloc(s) => {
                internal_vars.insert(s.var.clone());
            }
            SimpleLine::DecomposeBits(d) => {
                internal_vars.insert(d.var.clone());
            }
            SimpleLine::CounterHint(c) => {
                internal_vars.insert(c.var.clone());
            }
            SimpleLine::RawMemoryAccess(r) => {
                if let SimpleExpr::Var(var) = &r.res {
                    internal_vars.insert(var.clone());
                }
            }
            SimpleLine::FunctionCall(f) => {
                internal_vars.extend(f.return_data.iter().cloned());
            }
            SimpleLine::Branch(b) => {
                internal_vars.extend(find_internal_vars(&b.then_branch));
                internal_vars.extend(find_internal_vars(&b.else_branch));
            }
            SimpleLine::Panic(_)
            | SimpleLine::Print(_)
            | SimpleLine::Return(_)
            | SimpleLine::Precompile(_)
            | SimpleLine::LocationReport(_) => {
                // These instructions don't declare variables
            }
        }
    }

    internal_vars
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::HighLevelOperation;
    use crate::ir::VarOrConstMallocAccess;
    use crate::ir::simple_line::Assignment;
    use crate::ir::simple_line::Branch;
    use crate::ir::simple_line::CounterHint;
    use crate::ir::simple_line::DynamicAlloc;
    use crate::ir::simple_line::FunctionCall;
    use crate::ir::simple_line::LocationReport;
    use crate::ir::simple_line::Match;
    use crate::ir::simple_line::Panic;
    use crate::ir::simple_line::Print;
    use crate::ir::simple_line::RawMemoryAccess;
    use crate::ir::simple_line::Return;
    use crate::ir::simple_line::StaticAlloc;
    use crate::lang::{ConstExpression, SimpleExpr};

    #[test]
    fn test_find_internal_vars_empty() {
        let lines = vec![];
        let vars = find_internal_vars(&lines);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_find_internal_vars_assignment() {
        let lines = vec![SimpleLine::Assignment(Assignment {
            var: VarOrConstMallocAccess::Var("x".to_string()),
            operation: HighLevelOperation::Add,
            arg0: SimpleExpr::scalar(1),
            arg1: SimpleExpr::scalar(2),
        })];

        let vars = find_internal_vars(&lines);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("x"));
    }

    #[test]
    fn test_find_internal_vars_function_call() {
        let lines = vec![SimpleLine::FunctionCall(FunctionCall {
            function_name: "foo".to_string(),
            args: vec![SimpleExpr::scalar(42)],
            return_data: vec!["result1".to_string(), "result2".to_string()],
        })];

        let vars = find_internal_vars(&lines);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("result1"));
        assert!(vars.contains("result2"));
    }

    #[test]
    fn test_find_internal_vars_if_not_zero() {
        let lines = vec![SimpleLine::Branch(Branch {
            condition: SimpleExpr::Var("cond".to_string()),
            then_branch: vec![SimpleLine::Assignment(Assignment {
                var: VarOrConstMallocAccess::Var("then_var".to_string()),
                operation: HighLevelOperation::Add,
                arg0: SimpleExpr::scalar(1),
                arg1: SimpleExpr::scalar(0),
            })],
            else_branch: vec![SimpleLine::Assignment(Assignment {
                var: VarOrConstMallocAccess::Var("else_var".to_string()),
                operation: HighLevelOperation::Sub,
                arg0: SimpleExpr::scalar(2),
                arg1: SimpleExpr::scalar(0),
            })],
        })];

        let vars = find_internal_vars(&lines);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("then_var"));
        assert!(vars.contains("else_var"));
    }

    #[test]
    fn test_find_internal_vars_match() {
        let lines = vec![SimpleLine::Match(Match {
            value: SimpleExpr::Var("input".to_string()),
            arms: vec![
                vec![SimpleLine::Assignment(Assignment {
                    var: VarOrConstMallocAccess::Var("arm1_var".to_string()),
                    operation: HighLevelOperation::Mul,
                    arg0: SimpleExpr::scalar(3),
                    arg1: SimpleExpr::scalar(4),
                })],
                vec![SimpleLine::Assignment(Assignment {
                    var: VarOrConstMallocAccess::Var("arm2_var".to_string()),
                    operation: HighLevelOperation::Div,
                    arg0: SimpleExpr::scalar(8),
                    arg1: SimpleExpr::scalar(2),
                })],
            ],
        })];

        let vars = find_internal_vars(&lines);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("arm1_var"));
        assert!(vars.contains("arm2_var"));
    }

    #[test]
    fn test_find_internal_vars_various_malloc_types() {
        let lines = vec![
            SimpleLine::DynamicAlloc(DynamicAlloc {
                var: "hint_var".to_string(),
                size: SimpleExpr::scalar(10),
                vectorized: false,
                vectorized_len: SimpleExpr::scalar(0),
            }),
            SimpleLine::StaticAlloc(StaticAlloc {
                var: "const_var".to_string(),
                size: ConstExpression::scalar(20),
                label: 0,
            }),
            SimpleLine::CounterHint(CounterHint {
                var: "counter_var".to_string(),
            }),
        ];

        let vars = find_internal_vars(&lines);
        assert_eq!(vars.len(), 3);
        assert!(vars.contains("hint_var"));
        assert!(vars.contains("const_var"));
        assert!(vars.contains("counter_var"));
    }

    #[test]
    fn test_find_internal_vars_raw_access() {
        let lines = vec![SimpleLine::RawMemoryAccess(RawMemoryAccess {
            res: SimpleExpr::Var("raw_var".to_string()),
            index: SimpleExpr::scalar(5),
            shift: ConstExpression::scalar(1),
        })];

        let vars = find_internal_vars(&lines);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains("raw_var"));
    }

    #[test]
    fn test_find_internal_vars_no_op_instructions() {
        let lines = vec![
            SimpleLine::Panic(Panic),
            SimpleLine::Return(Return {
                return_data: vec![],
            }),
            SimpleLine::Print(Print {
                line_info: "test".to_string(),
                content: vec![SimpleExpr::scalar(42)],
            }),
            SimpleLine::LocationReport(LocationReport { location: 0 }),
        ];

        let vars = find_internal_vars(&lines);
        assert!(vars.is_empty());
    }
}
