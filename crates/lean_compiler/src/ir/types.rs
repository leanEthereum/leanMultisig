use crate::{
    ir::SimpleFunction,
    lang::{ConstExpression, ConstMallocLabel, SimpleExpr, Var},
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

/// Simple counter for generating unique identifiers.
#[derive(Debug, Clone, Default)]
pub struct Counter(pub usize);

impl Counter {
    /// Creates a new counter starting at 0.
    pub const fn new() -> Self {
        Self(0)
    }

    /// Returns the next value and increments the counter.
    pub fn next_value(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }
}

/// Simplified program representation after language simplification.
#[derive(Debug, Clone)]
pub struct SimpleProgram {
    pub functions: BTreeMap<String, SimpleFunction>,
}

/// Variable or constant malloc access for assignments.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VarOrConstMallocAccess {
    Var(Var),
    ConstMallocAccess {
        malloc_label: ConstMallocLabel,
        offset: ConstExpression,
    },
}

impl From<VarOrConstMallocAccess> for SimpleExpr {
    fn from(var_or_const: VarOrConstMallocAccess) -> Self {
        match var_or_const {
            VarOrConstMallocAccess::Var(var) => Self::Var(var),
            VarOrConstMallocAccess::ConstMallocAccess {
                malloc_label,
                offset,
            } => Self::ConstMallocAccess {
                malloc_label,
                offset,
            },
        }
    }
}

impl TryInto<VarOrConstMallocAccess> for SimpleExpr {
    type Error = ();

    fn try_into(self) -> Result<VarOrConstMallocAccess, Self::Error> {
        match self {
            Self::Var(var) => Ok(VarOrConstMallocAccess::Var(var)),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => Ok(VarOrConstMallocAccess::ConstMallocAccess {
                malloc_label,
                offset,
            }),
            _ => Err(()),
        }
    }
}

impl From<Var> for VarOrConstMallocAccess {
    fn from(var: Var) -> Self {
        Self::Var(var)
    }
}

/// Helper enum for array access operations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),                       // var = array[index]
    ArrayIsAssigned(crate::lang::Expression), // array[index] = expr
}

/// Internal state for various counters during simplification.
#[derive(Debug, Clone, Default)]
pub struct Counters {
    pub(crate) aux_vars: usize,
    pub(crate) loops: usize,
    pub(crate) unrolls: usize,
}

/// Array access management for optimization.
#[derive(Debug, Clone, Default)]
pub struct ArrayManager {
    pub(crate) counter: usize,
    pub(crate) aux_vars: BTreeMap<(SimpleExpr, crate::lang::Expression), Var>, // (array, index) -> aux_var
    pub(crate) valid: BTreeSet<Var>, // currently valid aux vars
}

impl ArrayManager {
    pub(crate) fn get_aux_var(
        &mut self,
        array: &SimpleExpr,
        index: &crate::lang::Expression,
    ) -> Var {
        if let Some(var) = self.aux_vars.get(&(array.clone(), index.clone())) {
            return var.clone();
        }
        let new_var = format!("@arr_aux_{}", self.counter);
        self.counter += 1;
        self.aux_vars
            .insert((array.clone(), index.clone()), new_var.clone());
        new_var
    }
}

/// Constant malloc optimization state.
#[derive(Debug, Clone, Default)]
pub struct ConstMalloc {
    pub(crate) counter: usize,
    pub(crate) map: BTreeMap<Var, ConstMallocLabel>,
    pub(crate) forbidden_vars: BTreeSet<Var>, // vars shared between branches of an if/else
}

// Display implementations for types
impl Display for VarOrConstMallocAccess {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(var) => write!(f, "{var}"),
            Self::ConstMallocAccess {
                malloc_label,
                offset,
            } => {
                write!(f, "ConstMallocAccess({malloc_label}, {offset})")
            }
        }
    }
}

impl Display for SimpleProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for function in self.functions.values() {
            if !first {
                writeln!(f)?;
            }
            write!(f, "{function}")?;
            first = false;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::SimpleLine;
    use crate::ir::simple_line::{
        Assignment, CounterHint, DecomposeBits, DynamicAlloc, FunctionCall, LocationReport, Match,
        Panic, PrecompileOp, Print, RawMemoryAccess, Return, StaticAlloc,
    };
    use crate::lang::{ConstExpression, SimpleExpr};
    use crate::precompiles::PRECOMPILES;

    #[test]
    fn test_var_or_const_malloc_access_from_var() {
        let var = "test_var".to_string();
        let access = VarOrConstMallocAccess::from(var.clone());

        assert_eq!(access, VarOrConstMallocAccess::Var(var));
    }

    #[test]
    fn test_var_or_const_malloc_access_from_to_simple_expr() {
        let var = "test_var".to_string();
        let access = VarOrConstMallocAccess::Var(var.clone());
        let simple_expr: SimpleExpr = access.into();

        assert_eq!(simple_expr, SimpleExpr::Var(var));
    }

    #[test]
    fn test_var_or_const_malloc_access_const_malloc_conversion() {
        let label = 42;
        let offset = ConstExpression::from(100);
        let access = VarOrConstMallocAccess::ConstMallocAccess {
            malloc_label: label,
            offset: offset.clone(),
        };
        let simple_expr: SimpleExpr = access.into();

        assert_eq!(
            simple_expr,
            SimpleExpr::ConstMallocAccess {
                malloc_label: label,
                offset,
            }
        );
    }

    #[test]
    fn test_simple_expr_try_into_var_or_const_malloc_access_var() {
        let var = "test_var".to_string();
        let simple_expr = SimpleExpr::Var(var.clone());
        let result: Result<VarOrConstMallocAccess, ()> = simple_expr.try_into();

        assert_eq!(result, Ok(VarOrConstMallocAccess::Var(var)));
    }

    #[test]
    fn test_simple_expr_try_into_var_or_const_malloc_access_const_malloc() {
        let label = 42;
        let offset = ConstExpression::from(100);
        let simple_expr = SimpleExpr::ConstMallocAccess {
            malloc_label: label,
            offset: offset.clone(),
        };
        let result: Result<VarOrConstMallocAccess, ()> = simple_expr.try_into();

        assert_eq!(
            result,
            Ok(VarOrConstMallocAccess::ConstMallocAccess {
                malloc_label: label,
                offset,
            })
        );
    }

    #[test]
    fn test_simple_expr_try_into_var_or_const_malloc_access_failure() {
        let simple_expr = SimpleExpr::Constant(ConstExpression::from(42));
        let result: Result<VarOrConstMallocAccess, ()> = simple_expr.try_into();

        assert_eq!(result, Err(()));
    }

    #[test]
    fn test_array_manager_get_aux_var_first_time() {
        let mut manager = ArrayManager::default();
        let array = SimpleExpr::Var("test_array".to_string());
        let index = crate::lang::Expression::scalar(10);

        let var = manager.get_aux_var(&array, &index);

        assert_eq!(var, "@arr_aux_0");
        assert_eq!(manager.counter, 1);
        assert!(
            manager
                .aux_vars
                .contains_key(&(array.clone(), index.clone()))
        );
    }

    #[test]
    fn test_array_manager_get_aux_var_repeated_access() {
        let mut manager = ArrayManager::default();
        let array = SimpleExpr::Var("test_array".to_string());
        let index = crate::lang::Expression::scalar(10);

        let var1 = manager.get_aux_var(&array, &index);
        let var2 = manager.get_aux_var(&array, &index);

        assert_eq!(var1, var2);
        assert_eq!(var1, "@arr_aux_0");
        assert_eq!(manager.counter, 1); // Should not increment for repeated access
    }

    #[test]
    fn test_array_manager_different_array_index_pairs() {
        let mut manager = ArrayManager::default();
        let array1 = SimpleExpr::Var("array1".to_string());
        let array2 = SimpleExpr::Var("array2".to_string());
        let index1 = crate::lang::Expression::scalar(10);
        let index2 = crate::lang::Expression::scalar(20);

        let var1 = manager.get_aux_var(&array1, &index1);
        let var2 = manager.get_aux_var(&array2, &index2);
        let var3 = manager.get_aux_var(&array1, &index2);

        assert_eq!(var1, "@arr_aux_0");
        assert_eq!(var2, "@arr_aux_1");
        assert_eq!(var3, "@arr_aux_2");
        assert_eq!(manager.counter, 3);
    }

    #[test]
    fn test_counters_default() {
        let counters = Counters::default();

        assert_eq!(counters.aux_vars, 0);
        assert_eq!(counters.loops, 0);
        assert_eq!(counters.unrolls, 0);
    }

    #[test]
    fn test_const_malloc_default() {
        let const_malloc = ConstMalloc::default();

        assert_eq!(const_malloc.counter, 0);
        assert!(const_malloc.map.is_empty());
        assert!(const_malloc.forbidden_vars.is_empty());
    }

    #[test]
    fn test_var_or_const_malloc_access_display_var() {
        let access = VarOrConstMallocAccess::Var("test_var".to_string());

        assert_eq!(format!("{}", access), "test_var");
    }

    #[test]
    fn test_var_or_const_malloc_access_display_const_malloc() {
        let access = VarOrConstMallocAccess::ConstMallocAccess {
            malloc_label: 42,
            offset: ConstExpression::from(100),
        };

        assert_eq!(format!("{}", access), "ConstMallocAccess(42, 100)");
    }

    #[test]
    fn test_simple_line_display_assignment() {
        let line = SimpleLine::Assignment(Assignment {
            var: VarOrConstMallocAccess::Var("x".to_string()),
            operation: crate::ir::HighLevelOperation::Add,
            arg0: SimpleExpr::Var("a".to_string()),
            arg1: SimpleExpr::Var("b".to_string()),
        });

        assert_eq!(format!("{}", line), "x = a + b");
    }

    #[test]
    fn test_simple_line_display_panic() {
        let line = SimpleLine::Panic(Panic);

        assert_eq!(format!("{}", line), "panic");
    }

    #[test]
    fn test_simple_line_display_function_call_no_return() {
        let line = SimpleLine::FunctionCall(FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![SimpleExpr::scalar(42), SimpleExpr::Var("x".to_string())],
            return_data: vec![],
        });

        assert_eq!(format!("{}", line), "test_func(42, x)");
    }

    #[test]
    fn test_simple_line_display_function_call_with_return() {
        let line = SimpleLine::FunctionCall(FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![SimpleExpr::scalar(42)],
            return_data: vec!["result".to_string()],
        });

        assert_eq!(format!("{}", line), "result = test_func(42)");
    }

    #[test]
    fn test_simple_line_display_function_ret() {
        let line = SimpleLine::Return(Return {
            return_data: vec![SimpleExpr::scalar(42), SimpleExpr::Var("x".to_string())],
        });

        assert_eq!(format!("{}", line), "return 42, x");
    }

    #[test]
    fn test_simple_line_display_counter_hint() {
        let line = SimpleLine::CounterHint(CounterHint {
            var: "counter".to_string(),
        });

        assert_eq!(format!("{}", line), "counter = counter_hint()");
    }

    #[test]
    fn test_simple_line_display_decompose_bits() {
        let line = SimpleLine::DecomposeBits(DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![SimpleExpr::scalar(255), SimpleExpr::Var("x".to_string())],
            label: 42,
        });

        assert_eq!(format!("{}", line), "bits = decompose_bits(255, x)");
    }

    #[test]
    fn test_simple_line_display_raw_access() {
        let line = SimpleLine::RawMemoryAccess(RawMemoryAccess {
            res: SimpleExpr::Var("result".to_string()),
            index: SimpleExpr::Var("ptr".to_string()),
            shift: ConstExpression::from(10),
        });

        assert_eq!(format!("{}", line), "memory[ptr + 10] = result");
    }

    #[test]
    fn test_simple_line_display_print() {
        let line = SimpleLine::Print(Print {
            line_info: "debug".to_string(),
            content: vec![SimpleExpr::scalar(42), SimpleExpr::Var("x".to_string())],
        });

        assert_eq!(format!("{}", line), "print(42, x)");
    }

    #[test]
    fn test_simple_line_display_hint_malloc_non_vectorized() {
        let line = SimpleLine::DynamicAlloc(DynamicAlloc {
            var: "ptr".to_string(),
            size: SimpleExpr::scalar(100),
            vectorized: false,
            vectorized_len: SimpleExpr::zero(),
        });

        assert_eq!(format!("{}", line), "ptr = malloc(100)");
    }

    #[test]
    fn test_simple_line_display_hint_malloc_vectorized() {
        let line = SimpleLine::DynamicAlloc(DynamicAlloc {
            var: "ptr".to_string(),
            size: SimpleExpr::scalar(100),
            vectorized: true,
            vectorized_len: SimpleExpr::scalar(8),
        });

        assert_eq!(format!("{}", line), "ptr = malloc_vec(100, 8)");
    }

    #[test]
    fn test_simple_line_display_const_malloc() {
        let line = SimpleLine::StaticAlloc(StaticAlloc {
            var: "ptr".to_string(),
            size: ConstExpression::from(100),
            label: 42,
        });

        assert_eq!(format!("{}", line), "ptr = malloc(100)");
    }

    #[test]
    fn test_simple_line_display_precompile() {
        let precompile = PRECOMPILES[0].clone();
        let line = SimpleLine::Precompile(PrecompileOp {
            precompile,
            args: vec![SimpleExpr::scalar(42)],
        });

        assert_eq!(format!("{}", line), format!("{}(42)", PRECOMPILES[0].name));
    }

    #[test]
    fn test_simple_line_display_location_report() {
        let line = SimpleLine::LocationReport(LocationReport { location: 42 });

        assert_eq!(format!("{}", line), ""); // LocationReport displays as empty
    }

    #[test]
    fn test_simple_line_display_match() {
        let line = SimpleLine::Match(Match {
            value: SimpleExpr::Var("x".to_string()),
            arms: vec![
                vec![SimpleLine::Panic(Panic)],
                vec![SimpleLine::Return(Return {
                    return_data: vec![],
                })],
            ],
        });

        let expected = "match x { 0 => [panic], 1 => [return ] }";
        assert_eq!(format!("{}", line), expected);
    }

    #[test]
    fn test_array_access_type_var_assigned() {
        let access_type = ArrayAccessType::VarIsAssigned("result".to_string());

        match access_type {
            ArrayAccessType::VarIsAssigned(var) => assert_eq!(var, "result"),
            _ => panic!("Expected VarIsAssigned"),
        }
    }

    #[test]
    fn test_array_access_type_array_assigned() {
        let expr = crate::lang::Expression::scalar(42);
        let access_type = ArrayAccessType::ArrayIsAssigned(expr.clone());

        match access_type {
            ArrayAccessType::ArrayIsAssigned(e) => assert_eq!(e, expr),
            _ => panic!("Expected ArrayIsAssigned"),
        }
    }
}
