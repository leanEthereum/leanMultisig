use crate::{
    ir::HighLevelOperation,
    lang::{ConstExpression, ConstMallocLabel, SimpleExpr, Var},
    precompiles::Precompile,
};
use lean_vm::SourceLineNumber;
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
    pub fn next(&mut self) -> usize {
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

/// Simplified function representation.
#[derive(Debug, Clone)]
pub struct SimpleFunction {
    pub name: String,
    pub arguments: Vec<Var>,
    pub n_returned_vars: usize,
    pub instructions: Vec<SimpleLine>,
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

/// Simplified language instruction representation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleLine {
    Match {
        value: SimpleExpr,
        arms: Vec<Vec<Self>>, // patterns = 0, 1, ...
    },
    Assignment {
        var: VarOrConstMallocAccess,
        operation: HighLevelOperation,
        arg0: SimpleExpr,
        arg1: SimpleExpr,
    },
    RawAccess {
        res: SimpleExpr,
        index: SimpleExpr,
        shift: ConstExpression,
    }, // res = memory[index + shift]
    IfNotZero {
        condition: SimpleExpr,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
    },
    FunctionCall {
        function_name: String,
        args: Vec<SimpleExpr>,
        return_data: Vec<Var>,
    },
    FunctionRet {
        return_data: Vec<SimpleExpr>,
    },
    Precompile {
        precompile: Precompile,
        args: Vec<SimpleExpr>,
    },
    Panic,
    // Hints
    DecomposeBits {
        var: Var, // a pointer to 31 * len(to_decompose) field elements, containing the bits of "to_decompose"
        to_decompose: Vec<SimpleExpr>,
        label: ConstMallocLabel,
    },
    CounterHint {
        var: Var,
    },
    Print {
        line_info: String,
        content: Vec<SimpleExpr>,
    },
    HintMAlloc {
        var: Var,
        size: SimpleExpr,
        vectorized: bool,
        vectorized_len: SimpleExpr,
    },
    ConstMalloc {
        // always not vectorized
        var: Var,
        size: ConstExpression,
        label: ConstMallocLabel,
    },
    // noop, debug purpose only
    LocationReport {
        location: SourceLineNumber,
    },
}

/// Helper enum for array access operations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),                       // var = array[index]
    ArrayIsAssigned(crate::lang::Expression), // array[index] = expr
}

/// Internal state for various counters during simplification.
#[derive(Debug, Clone, Default)]
pub(crate) struct Counters {
    pub(crate) aux_vars: usize,
    pub(crate) loops: usize,
    pub(crate) unrolls: usize,
}

/// Array access management for optimization.
#[derive(Debug, Clone, Default)]
pub(crate) struct ArrayManager {
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

impl Display for SimpleLine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}

impl SimpleLine {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::Match { value, arms } => {
                let arms_str = arms
                    .iter()
                    .enumerate()
                    .map(|(pattern, stmt)| {
                        format!(
                            "{} => {}",
                            pattern,
                            stmt.iter()
                                .map(|line| line.to_string_with_indent(indent + 1))
                                .collect::<Vec<_>>()
                                .join("\n")
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(", ");

                format!("match {value} {{\n{arms_str}\n{spaces}}}")
            }
            Self::Assignment {
                var,
                operation,
                arg0,
                arg1,
            } => {
                format!("{var} = {arg0} {operation} {arg1}")
            }
            Self::DecomposeBits {
                var: result,
                to_decompose,
                label: _,
            } => {
                format!(
                    "{} = decompose_bits({})",
                    result,
                    to_decompose
                        .iter()
                        .map(|expr| format!("{expr}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::CounterHint { var: result } => {
                format!("{result} = counter_hint()")
            }
            Self::RawAccess { res, index, shift } => {
                format!("memory[{index} + {shift}] = {res}")
            }
            Self::IfNotZero {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_str = then_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                let else_str = else_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                if else_branch.is_empty() {
                    format!("if {condition} != 0 {{\n{then_str}\n{spaces}}}")
                } else {
                    format!(
                        "if {condition} != 0 {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}"
                    )
                }
            }
            Self::FunctionCall {
                function_name,
                args,
                return_data,
            } => {
                let args_str = args
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(|var| var.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                if return_data.is_empty() {
                    format!("{function_name}({args_str})")
                } else {
                    format!("{return_data_str} = {function_name}({args_str})")
                }
            }
            Self::FunctionRet { return_data } => {
                let return_data_str = return_data
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {return_data_str}")
            }
            Self::Precompile { precompile, args } => {
                format!(
                    "{}({})",
                    &precompile.name,
                    args.iter()
                        .map(|arg| format!("{arg}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            Self::Print {
                line_info: _,
                content,
            } => {
                let content_str = content
                    .iter()
                    .map(|c| format!("{c}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("print({content_str})")
            }
            Self::HintMAlloc {
                var,
                size,
                vectorized,
                vectorized_len,
            } => {
                if *vectorized {
                    format!("{var} = malloc_vec({size}, {vectorized_len})")
                } else {
                    format!("{var} = malloc({size})")
                }
            }
            Self::ConstMalloc {
                var,
                size,
                label: _,
            } => {
                format!("{var} = malloc({size})")
            }
            Self::Panic => "panic".to_string(),
            Self::LocationReport { .. } => Default::default(),
        };
        format!("{spaces}{line_str}")
    }
}

impl Display for SimpleFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self
            .arguments
            .iter()
            .map(|arg| arg.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        let instructions_str = self
            .instructions
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.instructions.is_empty() {
            write!(
                f,
                "fn {}({}) -> {} {{}}",
                self.name, args_str, self.n_returned_vars
            )
        } else {
            write!(
                f,
                "fn {}({}) -> {} {{\n{}\n}}",
                self.name, args_str, self.n_returned_vars, instructions_str
            )
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
        let line = SimpleLine::Assignment {
            var: VarOrConstMallocAccess::Var("x".to_string()),
            operation: crate::ir::HighLevelOperation::Add,
            arg0: SimpleExpr::Var("a".to_string()),
            arg1: SimpleExpr::Var("b".to_string()),
        };

        assert_eq!(format!("{}", line), "x = a + b");
    }

    #[test]
    fn test_simple_line_display_panic() {
        let line = SimpleLine::Panic;

        assert_eq!(format!("{}", line), "panic");
    }

    #[test]
    fn test_simple_line_display_function_call_no_return() {
        let line = SimpleLine::FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![SimpleExpr::scalar(42), SimpleExpr::Var("x".to_string())],
            return_data: vec![],
        };

        assert_eq!(format!("{}", line), "test_func(42, x)");
    }

    #[test]
    fn test_simple_line_display_function_call_with_return() {
        let line = SimpleLine::FunctionCall {
            function_name: "test_func".to_string(),
            args: vec![SimpleExpr::scalar(42)],
            return_data: vec!["result".to_string()],
        };

        assert_eq!(format!("{}", line), "result = test_func(42)");
    }

    #[test]
    fn test_simple_line_display_function_ret() {
        let line = SimpleLine::FunctionRet {
            return_data: vec![SimpleExpr::scalar(42), SimpleExpr::Var("x".to_string())],
        };

        assert_eq!(format!("{}", line), "return 42, x");
    }

    #[test]
    fn test_simple_line_display_if_not_zero_no_else() {
        let line = SimpleLine::IfNotZero {
            condition: SimpleExpr::Var("x".to_string()),
            then_branch: vec![SimpleLine::Panic],
            else_branch: vec![],
        };

        let expected = "if x != 0 {\n    panic\n}";
        assert_eq!(format!("{}", line), expected);
    }

    #[test]
    fn test_simple_line_display_if_not_zero_with_else() {
        let line = SimpleLine::IfNotZero {
            condition: SimpleExpr::Var("x".to_string()),
            then_branch: vec![SimpleLine::Panic],
            else_branch: vec![SimpleLine::FunctionRet {
                return_data: vec![],
            }],
        };

        let expected = "if x != 0 {\n    panic\n} else {\n    return \n}";
        assert_eq!(format!("{}", line), expected);
    }

    #[test]
    fn test_simple_line_display_counter_hint() {
        let line = SimpleLine::CounterHint {
            var: "counter".to_string(),
        };

        assert_eq!(format!("{}", line), "counter = counter_hint()");
    }

    #[test]
    fn test_simple_line_display_decompose_bits() {
        let line = SimpleLine::DecomposeBits {
            var: "bits".to_string(),
            to_decompose: vec![SimpleExpr::scalar(255), SimpleExpr::Var("x".to_string())],
            label: 42,
        };

        assert_eq!(format!("{}", line), "bits = decompose_bits(255, x)");
    }

    #[test]
    fn test_simple_line_display_raw_access() {
        let line = SimpleLine::RawAccess {
            res: SimpleExpr::Var("result".to_string()),
            index: SimpleExpr::Var("ptr".to_string()),
            shift: ConstExpression::from(10),
        };

        assert_eq!(format!("{}", line), "memory[ptr + 10] = result");
    }

    #[test]
    fn test_simple_line_display_print() {
        let line = SimpleLine::Print {
            line_info: "debug".to_string(),
            content: vec![SimpleExpr::scalar(42), SimpleExpr::Var("x".to_string())],
        };

        assert_eq!(format!("{}", line), "print(42, x)");
    }

    #[test]
    fn test_simple_line_display_hint_malloc_non_vectorized() {
        let line = SimpleLine::HintMAlloc {
            var: "ptr".to_string(),
            size: SimpleExpr::scalar(100),
            vectorized: false,
            vectorized_len: SimpleExpr::zero(),
        };

        assert_eq!(format!("{}", line), "ptr = malloc(100)");
    }

    #[test]
    fn test_simple_line_display_hint_malloc_vectorized() {
        let line = SimpleLine::HintMAlloc {
            var: "ptr".to_string(),
            size: SimpleExpr::scalar(100),
            vectorized: true,
            vectorized_len: SimpleExpr::scalar(8),
        };

        assert_eq!(format!("{}", line), "ptr = malloc_vec(100, 8)");
    }

    #[test]
    fn test_simple_line_display_const_malloc() {
        let line = SimpleLine::ConstMalloc {
            var: "ptr".to_string(),
            size: ConstExpression::from(100),
            label: 42,
        };

        assert_eq!(format!("{}", line), "ptr = malloc(100)");
    }

    #[test]
    fn test_simple_line_display_precompile() {
        let precompile = PRECOMPILES[0].clone();
        let line = SimpleLine::Precompile {
            precompile,
            args: vec![SimpleExpr::scalar(42)],
        };

        assert_eq!(format!("{}", line), format!("{}(42)", PRECOMPILES[0].name));
    }

    #[test]
    fn test_simple_line_display_location_report() {
        let line = SimpleLine::LocationReport { location: 42 };

        assert_eq!(format!("{}", line), ""); // LocationReport displays as empty
    }

    #[test]
    fn test_simple_line_display_match() {
        let line = SimpleLine::Match {
            value: SimpleExpr::Var("x".to_string()),
            arms: vec![
                vec![SimpleLine::Panic],
                vec![SimpleLine::FunctionRet {
                    return_data: vec![],
                }],
            ],
        };

        let expected = "match x {\n0 =>     panic, 1 =>     return \n}";
        assert_eq!(format!("{}", line), expected);
    }

    #[test]
    fn test_simple_function_display_empty() {
        let function = SimpleFunction {
            name: "test".to_string(),
            arguments: vec!["x".to_string(), "y".to_string()],
            n_returned_vars: 1,
            instructions: vec![],
        };

        assert_eq!(format!("{}", function), "fn test(x, y) -> 1 {}");
    }

    #[test]
    fn test_simple_function_display_with_body() {
        let function = SimpleFunction {
            name: "test".to_string(),
            arguments: vec!["x".to_string()],
            n_returned_vars: 1,
            instructions: vec![SimpleLine::Panic],
        };

        assert_eq!(format!("{}", function), "fn test(x) -> 1 {\n    panic\n}");
    }

    #[test]
    fn test_simple_program_display_empty() {
        let program = SimpleProgram {
            functions: BTreeMap::new(),
        };

        assert_eq!(format!("{}", program), "");
    }

    #[test]
    fn test_simple_program_display_single_function() {
        let mut functions = BTreeMap::new();
        functions.insert(
            "test".to_string(),
            SimpleFunction {
                name: "test".to_string(),
                arguments: vec![],
                n_returned_vars: 0,
                instructions: vec![SimpleLine::Panic],
            },
        );

        let program = SimpleProgram { functions };

        assert_eq!(format!("{}", program), "fn test() -> 0 {\n    panic\n}");
    }

    #[test]
    fn test_simple_program_display_multiple_functions() {
        let mut functions = BTreeMap::new();
        functions.insert(
            "func1".to_string(),
            SimpleFunction {
                name: "func1".to_string(),
                arguments: vec![],
                n_returned_vars: 0,
                instructions: vec![],
            },
        );
        functions.insert(
            "func2".to_string(),
            SimpleFunction {
                name: "func2".to_string(),
                arguments: vec![],
                n_returned_vars: 0,
                instructions: vec![],
            },
        );

        let program = SimpleProgram { functions };

        assert_eq!(
            format!("{}", program),
            "fn func1() -> 0 {}\nfn func2() -> 0 {}"
        );
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
