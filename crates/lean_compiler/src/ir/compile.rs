//! Generic compilation trait for IR instructions.

use crate::{
    codegen::Compiler,
    ir::{IntermediateInstruction, IntermediateValue},
    lang::{SimpleExpr, Var},
};
use lean_vm::{Label, Operation};
use std::collections::BTreeSet;

/// Result type for compilation operations.
pub type CompileResult<T = Vec<IntermediateInstruction>> = Result<T, String>;

/// Compilation context shared across instruction compilers.
#[derive(Debug)]
pub struct CompileContext<'a> {
    /// The main compiler instance with bytecode generation state
    pub compiler: &'a mut Compiler,
    /// Optional jump target for control flow continuation
    pub final_jump: Option<Label>,
    /// Set of variables declared in current scope
    pub declared_vars: &'a mut BTreeSet<Var>,
}

impl<'a> CompileContext<'a> {
    /// Creates a new compilation context.
    pub fn new(
        compiler: &'a mut Compiler,
        final_jump: Option<Label>,
        declared_vars: &'a mut BTreeSet<Var>,
    ) -> Self {
        Self {
            compiler,
            final_jump,
            declared_vars,
        }
    }
}

/// Core trait for compiling instruction types into intermediate bytecode.
pub trait Compile {
    /// Compiles the instruction into intermediate bytecode.
    ///
    /// # Arguments
    /// * `ctx` - Compilation context containing compiler state and scope information
    /// * `remaining_lines` - Remaining SimpleLine instructions in the current block for control flow
    ///
    /// # Returns
    /// Vector of intermediate instructions or compilation error
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult;
}

pub fn mark_vars_as_declared<VoC: std::borrow::Borrow<SimpleExpr>>(
    vocs: &[VoC],
    declared: &mut BTreeSet<Var>,
) {
    for voc in vocs {
        if let SimpleExpr::Var(v) = voc.borrow() {
            declared.insert(v.clone());
        }
    }
}

pub fn validate_vars_declared<VoC: std::borrow::Borrow<SimpleExpr>>(
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

pub fn handle_const_malloc(
    declared_vars: &mut BTreeSet<Var>,
    instructions: &mut Vec<IntermediateInstruction>,
    compiler: &mut Compiler,
    var: &Var,
    size: usize,
    label: &crate::lang::ConstMallocLabel,
) {
    declared_vars.insert(var.clone());
    instructions.push(IntermediateInstruction::Computation {
        operation: Operation::Add,
        arg_a: IntermediateValue::Constant(compiler.stack_size.into()),
        arg_c: IntermediateValue::Fp,
        res: IntermediateValue::MemoryAfterFp {
            offset: compiler.get_offset(&var.clone().into()),
        },
    });
    compiler.const_mallocs.insert(*label, compiler.stack_size);
    compiler.stack_size += size;
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
