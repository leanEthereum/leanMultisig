//! Precompiled operation instruction implementation.

use crate::{
    codegen::Compiler,
    ir::{
        IntermediateInstruction, IntermediateValue,
        compile::{Compile, CompileContext, CompileResult, FindInternalVars},
    },
    lang::SimpleExpr,
    precompiles::{Precompile, PrecompileName},
};
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Precompiled cryptographic operations.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PrecompileOp {
    /// The precompiled function to invoke
    pub precompile: Precompile,
    /// Arguments to pass to the precompiled function
    pub args: Vec<SimpleExpr>,
}

impl Compile for PrecompileOp {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        _remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let mut instructions = Vec::new();

        match &self.precompile.name {
            PrecompileName::Poseidon16 => {
                compile_poseidon(&mut instructions, &self.args, ctx.compiler, true)?;
            }
            PrecompileName::Poseidon24 => {
                compile_poseidon(&mut instructions, &self.args, ctx.compiler, false)?;
            }
            PrecompileName::DotProduct => {
                instructions.push(IntermediateInstruction::DotProduct {
                    arg0: IntermediateValue::from_simple_expr(&self.args[0], ctx.compiler),
                    arg1: IntermediateValue::from_simple_expr(&self.args[1], ctx.compiler),
                    res: IntermediateValue::from_simple_expr(&self.args[2], ctx.compiler),
                    size: self.args[3].as_constant().unwrap(),
                });
            }
            PrecompileName::MultilinearEval => {
                instructions.push(IntermediateInstruction::MultilinearEval {
                    coeffs: IntermediateValue::from_simple_expr(&self.args[0], ctx.compiler),
                    point: IntermediateValue::from_simple_expr(&self.args[1], ctx.compiler),
                    res: IntermediateValue::from_simple_expr(&self.args[2], ctx.compiler),
                    n_vars: self.args[3].as_constant().unwrap(),
                });
            }
        }

        Ok(instructions)
    }
}

impl Display for PrecompileOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.precompile.name,
            self.args
                .iter()
                .map(|arg| format!("{}", arg))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl FindInternalVars for PrecompileOp {
    fn find_internal_vars(&self) -> BTreeSet<crate::lang::Var> {
        BTreeSet::new()
    }
}

impl crate::ir::simple_line::IndentedDisplay for PrecompileOp {}

fn compile_poseidon(
    instructions: &mut Vec<IntermediateInstruction>,
    args: &[SimpleExpr],
    compiler: &Compiler,
    over_16: bool, // otherwise over_24
) -> Result<(), String> {
    assert_eq!(args.len(), 3);

    let low_level_arg_a = IntermediateValue::from_simple_expr(&args[0], compiler);
    let low_level_arg_b = IntermediateValue::from_simple_expr(&args[1], compiler);
    let low_level_res = IntermediateValue::from_simple_expr(&args[2], compiler);

    if over_16 {
        instructions.push(IntermediateInstruction::Poseidon2_16 {
            arg_a: low_level_arg_a,
            arg_b: low_level_arg_b,
            res: low_level_res,
        });
    } else {
        instructions.push(IntermediateInstruction::Poseidon2_24 {
            arg_a: low_level_arg_a,
            arg_b: low_level_arg_b,
            res: low_level_res,
        });
    }

    Ok(())
}
