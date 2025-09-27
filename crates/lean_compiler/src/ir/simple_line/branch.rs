//! Conditional branching instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue, SimpleLine,
        compiler::{
            Compile, CompileContext, CompileResult, FindInternalVars, validate_vars_declared,
        },
        simple_line::compile_lines,
    },
    lang::{ConstExpression, SimpleExpr, Var},
};
use lean_vm::{Label, Operation};
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Conditional branching (if-not-zero) instruction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Branch {
    /// Condition expression to evaluate
    pub condition: SimpleExpr,
    /// Instructions to execute when condition != 0
    pub then_branch: Vec<SimpleLine>,
    /// Instructions to execute when condition == 0
    pub else_branch: Vec<SimpleLine>,
}

impl Compile for Branch {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        // Validate condition variable is declared
        validate_vars_declared(&[&self.condition], ctx.declared_vars)?;

        let if_id = ctx.compiler.if_counter;
        ctx.compiler.if_counter += 1;

        let (if_label, else_label, end_label) = (
            Label::if_label(if_id),
            Label::else_label(if_id),
            Label::if_else_end(if_id),
        );

        let mut instructions = Vec::new();

        // Generate condition evaluation logic using field inversion
        let condition_simplified =
            IntermediateValue::from_simple_expr(&self.condition, ctx.compiler);

        // Compute 1/c (or 0 if c is zero)
        let condition_inverse_offset = ctx.compiler.stack_size;
        ctx.compiler.stack_size += 1;
        instructions.push(IntermediateInstruction::Inverse {
            arg: condition_simplified.clone(),
            res_offset: condition_inverse_offset,
        });

        // Compute c * 1/c
        let product_offset = ctx.compiler.stack_size;
        ctx.compiler.stack_size += 1;
        instructions.push(IntermediateInstruction::Computation {
            operation: Operation::Mul,
            arg_a: condition_simplified.clone(),
            arg_c: IntermediateValue::MemoryAfterFp {
                offset: condition_inverse_offset.into(),
            },
            res: IntermediateValue::MemoryAfterFp {
                offset: product_offset.into(),
            },
        });

        // Compute 1 - (c * 1/c)
        let one_minus_product_offset = ctx.compiler.stack_size;
        ctx.compiler.stack_size += 1;
        instructions.push(IntermediateInstruction::Computation {
            operation: Operation::Add,
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: one_minus_product_offset.into(),
            },
            arg_c: IntermediateValue::MemoryAfterFp {
                offset: product_offset.into(),
            },
            res: ConstExpression::one().into(),
        });

        // Constraint: c * (1 - (c * 1/c)) = 0
        instructions.push(IntermediateInstruction::Computation {
            operation: Operation::Mul,
            arg_a: IntermediateValue::MemoryAfterFp {
                offset: one_minus_product_offset.into(),
            },
            arg_c: condition_simplified,
            res: ConstExpression::zero().into(),
        });

        // Generate conditional jumps
        instructions.push(IntermediateInstruction::JumpIfNotZero {
            condition: IntermediateValue::MemoryAfterFp {
                offset: product_offset.into(),
            },
            dest: IntermediateValue::label(if_label.clone()),
            updated_fp: None,
        });

        instructions.push(IntermediateInstruction::Jump {
            dest: IntermediateValue::label(else_label.clone()),
            updated_fp: None,
        });

        // Compile branches and handle variable declarations
        let original_stack = ctx.compiler.stack_size;
        compile_branches(
            self,
            ctx,
            &if_label,
            &else_label,
            &end_label,
            original_stack,
        )?;

        // Compile remaining instructions
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

/// Compiles both branches of the conditional.
fn compile_branches(
    instruction: &Branch,
    ctx: &mut CompileContext<'_>,
    if_label: &Label,
    else_label: &Label,
    end_label: &Label,
    original_stack: usize,
) -> Result<(), String> {
    // Compile then branch
    let mut then_declared_vars = ctx.declared_vars.clone();
    let then_instructions = compile_lines(
        &instruction.then_branch,
        ctx.compiler,
        Some(end_label.clone()),
        &mut then_declared_vars,
    )?;
    let then_stack = ctx.compiler.stack_size;

    // Reset stack and compile else branch
    ctx.compiler.stack_size = original_stack;
    let mut else_declared_vars = ctx.declared_vars.clone();
    let else_instructions = compile_lines(
        &instruction.else_branch,
        ctx.compiler,
        Some(end_label.clone()),
        &mut else_declared_vars,
    )?;
    let else_stack = ctx.compiler.stack_size;

    // Update stack size and declared variables
    ctx.compiler.stack_size = then_stack.max(else_stack);
    *ctx.declared_vars = then_declared_vars
        .intersection(&else_declared_vars)
        .cloned()
        .collect();

    // Store compiled branches in bytecode
    ctx.compiler
        .bytecode
        .insert(if_label.clone(), then_instructions);
    ctx.compiler
        .bytecode
        .insert(else_label.clone(), else_instructions);

    Ok(())
}

impl Display for Branch {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let then_str = self
            .then_branch
            .iter()
            .map(|line| format!("{}", line))
            .collect::<Vec<_>>()
            .join("; ");

        let else_str = self
            .else_branch
            .iter()
            .map(|line| format!("{}", line))
            .collect::<Vec<_>>()
            .join("; ");

        if self.else_branch.is_empty() {
            write!(f, "if {} != 0 {{ {} }}", self.condition, then_str)
        } else {
            write!(
                f,
                "if {} != 0 {{ {} }} else {{ {} }}",
                self.condition, then_str, else_str
            )
        }
    }
}

impl FindInternalVars for Branch {
    fn find_internal_vars(&self) -> BTreeSet<Var> {
        let mut vars = BTreeSet::new();
        for line in &self.then_branch {
            vars.extend(line.find_internal_vars());
        }
        for line in &self.else_branch {
            vars.extend(line.find_internal_vars());
        }
        vars
    }
}

impl crate::ir::simple_line::IndentedDisplay for Branch {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let then_str = self
            .then_branch
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");

        let else_str = self
            .else_branch
            .iter()
            .map(|line| line.to_string_with_indent(indent + 1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.else_branch.is_empty() {
            format!(
                "{}if {} != 0 {{\n{}\n{}}}",
                spaces, self.condition, then_str, spaces
            )
        } else {
            format!(
                "{}if {} != 0 {{\n{}\n{}}} else {{\n{}\n{}}}",
                spaces, self.condition, then_str, spaces, else_str, spaces
            )
        }
    }
}
