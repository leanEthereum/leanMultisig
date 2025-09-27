//! Variable assignment instruction implementation.

use crate::{
    ir::{
        compile::{Compile, CompileContext, CompileResult, FindInternalVars},
        {HighLevelOperation, IntermediateInstruction, IntermediateValue, VarOrConstMallocAccess},
    },
    lang::{SimpleExpr, Var},
};
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Variable assignment with binary operations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Assignment {
    /// Target variable or const malloc access for assignment
    pub var: VarOrConstMallocAccess,
    /// Binary operation to perform
    pub operation: HighLevelOperation,
    /// First operand of the operation
    pub arg0: SimpleExpr,
    /// Second operand of the operation
    pub arg1: SimpleExpr,
}

impl Compile for Assignment {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let intermediate_instruction = IntermediateInstruction::computation(
            self.operation,
            IntermediateValue::from_simple_expr(&self.arg0, ctx.compiler),
            IntermediateValue::from_simple_expr(&self.arg1, ctx.compiler),
            IntermediateValue::from_var_or_const_malloc_access(&self.var, ctx.compiler),
        );

        // Mark operand variables as declared if they're variables
        crate::ir::compile::mark_vars_as_declared(&[&self.arg0, &self.arg1], ctx.declared_vars);

        // Mark target variable as declared if it's a variable
        if let VarOrConstMallocAccess::Var(var) = &self.var {
            ctx.declared_vars.insert(var.clone());
        }

        Ok(vec![intermediate_instruction])
    }
}

impl Display for Assignment {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} = {} {} {}",
            self.var, self.arg0, self.operation, self.arg1
        )
    }
}

impl FindInternalVars for Assignment {
    fn find_internal_vars(&self) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        if let VarOrConstMallocAccess::Var(var) = &self.var {
            vars.insert(var.clone());
        }
        vars
    }
}

impl crate::ir::simple_line::IndentedDisplay for Assignment {}
