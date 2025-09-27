//! Bit decomposition instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue,
        compile::{Compile, CompileContext, CompileResult, FindInternalVars, handle_const_malloc},
    },
    lang::{ConstMallocLabel, SimpleExpr, Var},
};
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Bit decomposition for field elements.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DecomposeBits {
    /// Variable to store the decomposed bits pointer
    pub var: Var,
    /// Expressions to decompose into bits
    pub to_decompose: Vec<SimpleExpr>,
    /// Label for the constant allocation of bit storage
    pub label: ConstMallocLabel,
}

impl Compile for DecomposeBits {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        use lean_vm::F;
        use p3_field::Field;

        let mut instructions = Vec::new();

        // Add bit decomposition instruction
        instructions.push(IntermediateInstruction::DecomposeBits {
            res_offset: ctx.compiler.stack_size,
            to_decompose: self
                .to_decompose
                .iter()
                .map(|expr| IntermediateValue::from_simple_expr(expr, ctx.compiler))
                .collect(),
        });

        // Use helper function to handle constant malloc for bit storage
        handle_const_malloc(
            ctx.declared_vars,
            &mut instructions,
            ctx.compiler,
            &self.var,
            F::bits() * self.to_decompose.len(),
            &self.label,
        );

        Ok(instructions)
    }
}

impl Display for DecomposeBits {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} = decompose_bits({})",
            self.var,
            self.to_decompose
                .iter()
                .map(|expr| format!("{}", expr))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl FindInternalVars for DecomposeBits {
    fn find_internal_vars(&self) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        vars.insert(self.var.clone());
        vars
    }
}

impl crate::ir::simple_line::IndentedDisplay for DecomposeBits {}
