//! Array assignment statement implementation.

use crate::{
    F,
    lang::{
        expr::{Expression, SimpleExpr},
        values::Var,
    },
    traits::IndentedDisplay,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

use super::traits::StatementAnalysis;

/// Array element assignment statement.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArrayAssign {
    /// Target array expression
    pub array: SimpleExpr,
    /// Index expression
    pub index: Expression,
    /// Value expression to assign
    pub value: Expression,
}

impl Display for ArrayAssign {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}] = {}", self.array, self.index, self.value)
    }
}

impl IndentedDisplay for ArrayAssign {}

impl StatementAnalysis for ArrayAssign {
    fn replace_vars_for_unroll(
        &mut self,
        iterator: &Var,
        unroll_index: usize,
        iterator_value: usize,
        internal_vars: &BTreeSet<Var>,
    ) {
        // arr[index] = value
        if let SimpleExpr::Var(array_var) = &mut self.array {
            assert!(array_var != iterator, "Weird");
            if internal_vars.contains(array_var) {
                *array_var = format!("@unrolled_{unroll_index}_{iterator_value}_{array_var}");
            }
        }
        crate::ir::unroll::replace_vars_for_unroll_in_expr(
            &mut self.index,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
        crate::ir::unroll::replace_vars_for_unroll_in_expr(
            &mut self.value,
            iterator,
            unroll_index,
            iterator_value,
            internal_vars,
        );
    }

    fn replace_vars_with_const(&mut self, map: &BTreeMap<Var, F>) {
        crate::ir::utilities::replace_vars_by_const_in_expr(
            &mut Expression::Value(self.array.clone()),
            map,
        );
        crate::ir::utilities::replace_vars_by_const_in_expr(&mut self.index, map);
        crate::ir::utilities::replace_vars_by_const_in_expr(&mut self.value, map);
    }

    fn find_internal_vars(&self) -> (BTreeSet<Var>, BTreeSet<Var>) {
        let mut internal_vars = BTreeSet::new();
        let mut external_vars = BTreeSet::new();

        // Array assignment doesn't create new internal variables, it modifies existing ones
        if let SimpleExpr::Var(array_var) = &self.array {
            external_vars.insert(array_var.clone());
        }

        let (index_internal, index_external) =
            crate::ir::utilities::find_internal_vars_in_expr(&self.index);
        internal_vars.extend(index_internal);
        external_vars.extend(index_external);

        let (value_internal, value_external) =
            crate::ir::utilities::find_internal_vars_in_expr(&self.value);
        internal_vars.extend(value_internal);
        external_vars.extend(value_external);

        (internal_vars, external_vars)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lang::expr::{Expression, SimpleExpr};

    #[test]
    fn test_array_assign_display() {
        let array_assign = ArrayAssign {
            array: SimpleExpr::Var("arr".to_string()),
            index: Expression::scalar(0),
            value: Expression::scalar(10),
        };
        assert_eq!(array_assign.to_string(), "arr[0] = 10");
    }

    #[test]
    fn test_array_assign_indented_display() {
        let array_assign = ArrayAssign {
            array: SimpleExpr::Var("data".to_string()),
            index: Expression::scalar(5),
            value: Expression::scalar(42),
        };
        assert_eq!(
            array_assign.to_string_with_indent(2),
            "        data[5] = 42"
        );
    }
}
