//! Function call instruction implementation.

use crate::{
    ir::{
        IntermediateInstruction, IntermediateValue,
        compiler::{
            Compile, CompileContext, CompileResult, Compiler, FindInternalVars,
            validate_vars_declared,
        },
        simple_line::compile_lines,
    },
    lang::{ConstExpression, SimpleExpr, Var},
};
use lean_vm::Label;
use std::{
    collections::BTreeSet,
    fmt::{Display, Formatter},
};

/// Function invocation with argument passing.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionCall {
    /// Name of the function to call
    pub function_name: String,
    /// Arguments to pass to the function
    pub args: Vec<SimpleExpr>,
    /// Variables to store return values
    pub return_data: Vec<Var>,
}

impl Compile for FunctionCall {
    fn compile(
        &self,
        ctx: &mut CompileContext<'_>,
        remaining_lines: &[crate::ir::SimpleLine],
    ) -> CompileResult {
        let call_id = ctx.compiler.call_counter;
        ctx.compiler.call_counter += 1;
        let return_label = Label::return_from_call(call_id);

        let new_fp_pos = ctx.compiler.stack_size;
        ctx.compiler.stack_size += 1;

        // Setup function call
        let instructions = setup_function_call(
            &self.function_name,
            &self.args,
            new_fp_pos,
            &return_label,
            ctx.compiler,
        )?;

        // Validate arguments are declared
        validate_vars_declared(&self.args, ctx.declared_vars)?;

        // Mark return variables as declared
        ctx.declared_vars.extend(self.return_data.iter().cloned());

        // Compile instructions after function call
        let after_call = {
            let mut after_instructions = Vec::new();

            // Copy return values
            for (i, ret_var) in self.return_data.iter().enumerate() {
                after_instructions.push(IntermediateInstruction::Deref {
                    shift_0: new_fp_pos.into(),
                    shift_1: (2 + self.args.len() + i).into(),
                    res: crate::ir::IntermediaryMemOrFpOrConstant::MemoryAfterFp {
                        offset: ctx.compiler.get_offset(&ret_var.clone().into()),
                    },
                });
            }

            // Continue with remaining instructions
            after_instructions.extend(compile_lines(
                remaining_lines,
                ctx.compiler,
                ctx.final_jump.clone(),
                ctx.declared_vars,
            )?);

            after_instructions
        };

        // Insert the return continuation into bytecode
        ctx.compiler.bytecode.insert(return_label, after_call);

        Ok(instructions)
    }
}

impl Display for FunctionCall {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self
            .args
            .iter()
            .map(|arg| format!("{}", arg))
            .collect::<Vec<_>>()
            .join(", ");
        let return_data_str = self
            .return_data
            .iter()
            .map(|var| var.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        if self.return_data.is_empty() {
            write!(f, "{}({})", self.function_name, args_str)
        } else {
            write!(
                f,
                "{} = {}({})",
                return_data_str, self.function_name, args_str
            )
        }
    }
}

impl FindInternalVars for FunctionCall {
    fn find_internal_vars(&self) -> BTreeSet<Var> {
        self.return_data.iter().cloned().collect()
    }
}

impl crate::ir::simple_line::IndentedDisplay for FunctionCall {}

fn setup_function_call(
    func_name: &str,
    args: &[SimpleExpr],
    new_fp_pos: usize,
    return_label: &Label,
    compiler: &Compiler,
) -> Result<Vec<IntermediateInstruction>, String> {
    let mut instructions = vec![
        IntermediateInstruction::RequestMemory {
            offset: new_fp_pos.into(),
            size: ConstExpression::function_size(Label::function(func_name)).into(),
            vectorized: false,
            vectorized_len: IntermediateValue::Constant(ConstExpression::zero()),
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::zero(),
            res: crate::ir::IntermediaryMemOrFpOrConstant::Constant(ConstExpression::label(
                return_label.clone(),
            )),
        },
        IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: ConstExpression::one(),
            res: crate::ir::IntermediaryMemOrFpOrConstant::Fp,
        },
    ];

    // Copy arguments
    for (i, arg) in args.iter().enumerate() {
        instructions.push(IntermediateInstruction::Deref {
            shift_0: new_fp_pos.into(),
            shift_1: (2 + i).into(),
            res: arg.to_mem_after_fp_or_constant(compiler),
        });
    }

    instructions.push(IntermediateInstruction::Jump {
        dest: IntermediateValue::label(Label::function(func_name)),
        updated_fp: Some(IntermediateValue::MemoryAfterFp {
            offset: new_fp_pos.into(),
        }),
    });

    Ok(instructions)
}
