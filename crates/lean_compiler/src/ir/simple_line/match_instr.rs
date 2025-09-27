//! Pattern matching instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue, SimpleLine,
        compile::{Compile, CompileContext, CompileResult},
        simple_line::compile_lines,
    },
    lang::{ConstExpression, SimpleExpr},
};
use lean_vm::{Label, Operation};
use std::fmt::{Display, Formatter};

/// Pattern matching with computed jumps.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Match {
    /// Expression to match against
    pub value: SimpleExpr,
    /// Match arms, each containing a sequence of instructions
    pub arms: Vec<Vec<SimpleLine>>,
}

impl Compile for Match {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let match_index = ctx.compiler.match_blocks.len();
        let end_label = Label::match_end(match_index);
        let value_simplified = IntermediateValue::from_simple_expr(&self.value, ctx.compiler);

        let mut instructions = Vec::new();
        let mut compiled_arms = Vec::new();
        let original_stack_size = ctx.compiler.stack_size;
        let mut max_stack_size = original_stack_size;

        // Compile each match arm
        for (i, arm) in self.arms.iter().enumerate() {
            let mut arm_declared_vars = ctx.declared_vars.clone();
            ctx.compiler.stack_size = original_stack_size;

            let arm_instructions = compile_lines(
                arm,
                ctx.compiler,
                Some(end_label.clone()),
                &mut arm_declared_vars,
            )?;
            compiled_arms.push(arm_instructions);
            max_stack_size = ctx.compiler.stack_size.max(max_stack_size);

            // Update declared variables - only variables declared in all arms are globally declared
            *ctx.declared_vars = if i == 0 {
                arm_declared_vars
            } else {
                ctx.declared_vars
                    .intersection(&arm_declared_vars)
                    .cloned()
                    .collect()
            };
        }

        ctx.compiler.stack_size = max_stack_size;
        ctx.compiler.match_blocks.push(compiled_arms);

        // Generate jump table logic
        generate_jump_table(&mut instructions, ctx, match_index, value_simplified)?;

        // Compile remaining instructions after match
        let remaining_instructions = compile_lines(
            remaining_lines,
            ctx.compiler,
            ctx.final_jump.clone(),
            ctx.declared_vars,
        )?;
        ctx.compiler
            .bytecode
            .insert(end_label, remaining_instructions);

        Ok(instructions)
    }
}

/// Generates the jump table logic for pattern matching.
fn generate_jump_table(
    instructions: &mut Vec<IntermediateInstruction>,
    ctx: &mut CompileContext<'_>,
    match_index: usize,
    value_simplified: IntermediateValue,
) -> Result<(), String> {
    // value * block_size
    let value_scaled_offset = IntermediateValue::MemoryAfterFp {
        offset: ctx.compiler.stack_size.into(),
    };
    ctx.compiler.stack_size += 1;

    instructions.push(IntermediateInstruction::Computation {
        operation: Operation::Mul,
        arg_a: value_simplified,
        arg_c: ConstExpression::Value(crate::lang::ConstantValue::MatchBlockSize { match_index })
            .into(),
        res: value_scaled_offset.clone(),
    });

    // scaled_value + first_block_start
    let jump_dest_offset = IntermediateValue::MemoryAfterFp {
        offset: ctx.compiler.stack_size.into(),
    };
    ctx.compiler.stack_size += 1;

    instructions.push(IntermediateInstruction::Computation {
        operation: Operation::Add,
        arg_a: value_scaled_offset,
        arg_c: ConstExpression::Value(crate::lang::ConstantValue::MatchFirstBlockStart {
            match_index,
        })
        .into(),
        res: jump_dest_offset.clone(),
    });

    // Jump to computed destination
    instructions.push(IntermediateInstruction::Jump {
        dest: jump_dest_offset,
        updated_fp: None,
    });

    Ok(())
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let arms_str = self
            .arms
            .iter()
            .enumerate()
            .map(|(pattern, stmt)| {
                let stmt_str = stmt
                    .iter()
                    .map(|line| format!("{}", line))
                    .collect::<Vec<_>>()
                    .join("; ");
                format!("{} => [{}]", pattern, stmt_str)
            })
            .collect::<Vec<_>>()
            .join(", ");

        write!(f, "match {} {{ {} }}", self.value, arms_str)
    }
}

impl crate::ir::simple_line::IndentedDisplay for Match {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let arms_str = self
            .arms
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
        format!(
            "{}match {} {{\n{}\n{}}}",
            spaces, self.value, arms_str, spaces
        )
    }
}
