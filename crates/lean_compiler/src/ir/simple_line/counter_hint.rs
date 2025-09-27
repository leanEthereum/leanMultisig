//! Counter hint instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction,
        compiler::{Compile, CompileContext, CompileResult, FindInternalVars},
    },
    lang::Var,
};
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};
use utils::ToUsize;

/// Counter value hint for loops.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CounterHint {
    /// Variable to store the counter hint value
    pub var: Var,
}

impl Compile for CounterHint {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        ctx.declared_vars.insert(self.var.clone());

        let instruction = IntermediateInstruction::CounterHint {
            res_offset: ctx
                .compiler
                .get_offset(&self.var.clone().into())
                .naive_eval()
                .unwrap()
                .to_usize(),
        };

        Ok(vec![instruction])
    }
}

impl Display for CounterHint {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} = counter_hint()", self.var)
    }
}

impl FindInternalVars for CounterHint {
    fn find_internal_vars(&self) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        vars.insert(self.var.clone());
        vars
    }
}

impl crate::ir::simple_line::IndentedDisplay for CounterHint {}
