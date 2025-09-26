use crate::lang::*;
use std::{borrow::Borrow, collections::BTreeSet};

/// Marks variables as declared in the declaration tracking set.
///
/// This helper function extracts variables from expressions and adds them
/// to the declared variables set for tracking purposes.
pub fn mark_vars_as_declared<VoC: Borrow<SimpleExpr>>(vocs: &[VoC], declared: &mut BTreeSet<Var>) {
    for voc in vocs {
        if let SimpleExpr::Var(v) = voc.borrow() {
            declared.insert(v.clone());
        }
    }
}

/// Validates that all variables in expressions are declared.
///
/// This function checks that all variable references have been declared
/// before use, helping catch undeclared variable errors during compilation.
pub fn validate_vars_declared<VoC: Borrow<SimpleExpr>>(
    vocs: &[VoC],
    declared: &BTreeSet<Var>,
) -> Result<(), String> {
    for voc in vocs {
        if let SimpleExpr::Var(v) = voc.borrow()
            && !declared.contains(v)
        {
            return Err(format!("Variable {v} not declared"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn test_mark_vars_as_declared_empty() {
        let exprs: Vec<SimpleExpr> = vec![];
        let mut declared = BTreeSet::new();

        mark_vars_as_declared(&exprs, &mut declared);
        assert!(declared.is_empty());
    }

    #[test]
    fn test_mark_vars_as_declared_variables() {
        let exprs = vec![
            SimpleExpr::Var("x".to_string()),
            SimpleExpr::Var("y".to_string()),
            SimpleExpr::scalar(42), // Should be ignored
        ];
        let mut declared = BTreeSet::new();

        mark_vars_as_declared(&exprs, &mut declared);
        assert_eq!(declared.len(), 2);
        assert!(declared.contains("x"));
        assert!(declared.contains("y"));
    }

    #[test]
    fn test_mark_vars_as_declared_constants_ignored() {
        let exprs = vec![SimpleExpr::scalar(10), SimpleExpr::scalar(20)];
        let mut declared = BTreeSet::new();

        mark_vars_as_declared(&exprs, &mut declared);
        assert!(declared.is_empty());
    }

    #[test]
    fn test_validate_vars_declared_success() {
        let mut declared = BTreeSet::new();
        declared.insert("x".to_string());
        declared.insert("y".to_string());

        let exprs = vec![
            SimpleExpr::Var("x".to_string()),
            SimpleExpr::Var("y".to_string()),
            SimpleExpr::scalar(42),
        ];

        let result = validate_vars_declared(&exprs, &declared);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_vars_declared_undeclared_variable() {
        let mut declared = BTreeSet::new();
        declared.insert("x".to_string());

        let exprs = vec![
            SimpleExpr::Var("x".to_string()),
            SimpleExpr::Var("z".to_string()), // Undeclared
        ];

        let result = validate_vars_declared(&exprs, &declared);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Variable z not declared"));
    }

    #[test]
    fn test_validate_vars_declared_empty_sets() {
        let declared = BTreeSet::new();
        let exprs: Vec<SimpleExpr> = vec![];

        let result = validate_vars_declared(&exprs, &declared);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_vars_declared_constants_always_valid() {
        let declared = BTreeSet::new(); // No declared variables

        let exprs = vec![SimpleExpr::scalar(42), SimpleExpr::scalar(100)];

        let result = validate_vars_declared(&exprs, &declared);
        assert!(result.is_ok());
    }

    #[test]
    fn test_validate_vars_declared_mixed_valid_invalid() {
        let mut declared = BTreeSet::new();
        declared.insert("valid".to_string());

        let exprs = vec![
            SimpleExpr::Var("valid".to_string()),
            SimpleExpr::scalar(10),
            SimpleExpr::Var("invalid".to_string()),
        ];

        let result = validate_vars_declared(&exprs, &declared);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .contains("Variable invalid not declared")
        );
    }
}
