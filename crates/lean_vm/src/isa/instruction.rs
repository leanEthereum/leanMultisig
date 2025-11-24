//! VM instruction definitions

use super::Operation;
use super::operands::{MemOrConstant, MemOrFp, MemOrFpOrConstant};
use crate::core::{F, Label};
use crate::diagnostics::RunnerError;
use crate::execution::Memory;
use crate::tables::TableT;
use crate::{N_TABLES, Table, TableTrace};
use multilinear_toolkit::prelude::*;
use std::fmt::{Display, Formatter};
use utils::ToUsize;

/// Complete set of VM instruction types with comprehensive operation support
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction {
    /// Basic arithmetic computation instruction (ADD, MUL)
    Computation {
        /// The arithmetic operation to perform
        operation: Operation,
        /// First operand (can be constant or memory location)
        arg_a: MemOrConstant,
        /// Second operand (can be memory location or frame pointer)
        arg_c: MemOrFp,
        /// Result destination (can be constant or memory location)
        res: MemOrConstant,
    },

    /// Memory dereference instruction: res = m[m[fp + shift_0] + shift_1]
    Deref {
        /// First offset from frame pointer for base address
        shift_0: usize,
        /// Second offset added to dereferenced base address
        shift_1: usize,
        /// Result destination (can be memory, frame pointer, or constant)
        res: MemOrFpOrConstant,
    },

    /// Conditional jump instruction for control flow
    Jump {
        /// Jump condition (jump if non-zero)
        condition: MemOrConstant,
        /// Jump destination label (for debugging purposes)
        label: Label,
        /// Jump destination address
        dest: MemOrConstant,
        /// New frame pointer value after jump
        updated_fp: MemOrFp,
    },

    Precompile {
        table: Table,
        arg_a: MemOrConstant,
        arg_b: MemOrConstant,
        arg_c: MemOrFp,
        aux: usize,
    },
}

/// Execution context for instruction processing
#[derive(Debug)]
pub struct InstructionContext<'a> {
    pub memory: &'a mut Memory,
    pub fp: &'a mut usize,
    pub pc: &'a mut usize,
    pub pcs: &'a Vec<usize>,
    pub traces: &'a mut [TableTrace; N_TABLES],
    pub add_counts: &'a mut usize,
    pub mul_counts: &'a mut usize,
    pub deref_counts: &'a mut usize,
    pub jump_counts: &'a mut usize,
    pub poseidon16_precomputed: &'a [([F; 16], [F; 16])],
    pub poseidon24_precomputed: &'a [([F; 24], [F; 8])],
    pub n_poseidon16_precomputed_used: &'a mut usize,
    pub n_poseidon24_precomputed_used: &'a mut usize,
}

impl Instruction {
    /// Execute this instruction within the given execution context
    #[inline(always)]
    pub fn execute_instruction(&self, ctx: &mut InstructionContext<'_>) -> Result<(), RunnerError> {
        match self {
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                if res.is_value_unknown(ctx.memory, *ctx.fp) {
                    let memory_address_res = res.memory_address(*ctx.fp)?;
                    let a_value = arg_a.read_value(ctx.memory, *ctx.fp)?;
                    let b_value = arg_c.read_value(ctx.memory, *ctx.fp)?;
                    let res_value = operation.compute(a_value, b_value);
                    ctx.memory.set(memory_address_res, res_value)?;
                } else if arg_a.is_value_unknown(ctx.memory, *ctx.fp) {
                    let memory_address_a = arg_a.memory_address(*ctx.fp)?;
                    let res_value = res.read_value(ctx.memory, *ctx.fp)?;
                    let b_value = arg_c.read_value(ctx.memory, *ctx.fp)?;
                    let a_value = operation
                        .inverse_compute(res_value, b_value)
                        .ok_or(RunnerError::DivByZero)?;
                    ctx.memory.set(memory_address_a, a_value)?;
                } else if arg_c.is_value_unknown(ctx.memory, *ctx.fp) {
                    let memory_address_b = arg_c.memory_address(*ctx.fp)?;
                    let res_value = res.read_value(ctx.memory, *ctx.fp)?;
                    let a_value = arg_a.read_value(ctx.memory, *ctx.fp)?;
                    let b_value = operation
                        .inverse_compute(res_value, a_value)
                        .ok_or(RunnerError::DivByZero)?;
                    ctx.memory.set(memory_address_b, b_value)?;
                } else {
                    let a_value = arg_a.read_value(ctx.memory, *ctx.fp)?;
                    let b_value = arg_c.read_value(ctx.memory, *ctx.fp)?;
                    let res_value = res.read_value(ctx.memory, *ctx.fp)?;
                    let computed_value = operation.compute(a_value, b_value);
                    if res_value != computed_value {
                        return Err(RunnerError::NotEqual(computed_value, res_value));
                    }
                }

                match operation {
                    Operation::Add => *ctx.add_counts += 1,
                    Operation::Mul => *ctx.mul_counts += 1,
                }

                *ctx.pc += 1;
                Ok(())
            }
            Self::Deref { shift_0, shift_1, res } => {
                if res.is_value_unknown(ctx.memory, *ctx.fp) {
                    let memory_address_res = res.memory_address(*ctx.fp)?;
                    let ptr = ctx.memory.get(*ctx.fp + shift_0)?;
                    let value = ctx.memory.get(ptr.to_usize() + shift_1)?;
                    ctx.memory.set(memory_address_res, value)?;
                } else {
                    let value = res.read_value(ctx.memory, *ctx.fp)?;
                    let ptr = ctx.memory.get(*ctx.fp + shift_0)?;
                    ctx.memory.set(ptr.to_usize() + shift_1, value)?;
                }

                *ctx.deref_counts += 1;
                *ctx.pc += 1;
                Ok(())
            }
            Self::Jump {
                condition,
                label: _,
                dest,
                updated_fp,
            } => {
                let condition_value = condition.read_value(ctx.memory, *ctx.fp)?;
                assert!([F::ZERO, F::ONE].contains(&condition_value),);
                if condition_value == F::ZERO {
                    *ctx.pc += 1;
                } else {
                    *ctx.pc = dest.read_value(ctx.memory, *ctx.fp)?.to_usize();
                    *ctx.fp = updated_fp.read_value(ctx.memory, *ctx.fp)?.to_usize();
                }

                *ctx.jump_counts += 1;
                Ok(())
            }

            Self::Precompile {
                table,
                arg_a,
                arg_b,
                arg_c,
                aux: size,
            } => {
                table.execute(
                    arg_a.read_value(ctx.memory, *ctx.fp)?,
                    arg_b.read_value(ctx.memory, *ctx.fp)?,
                    arg_c.read_value(ctx.memory, *ctx.fp)?,
                    *size,
                    ctx,
                )?;

                *ctx.pc += 1;
                Ok(())
            }
        }
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                write!(f, "{res} = {arg_a} {operation} {arg_c}")
            }
            Self::Deref { shift_0, shift_1, res } => {
                write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]")
            }
            Self::Jump {
                condition,
                label,
                dest,
                updated_fp,
            } => {
                write!(
                    f,
                    "if {condition} != 0 jump to {label} = {dest} with next(fp) = {updated_fp}"
                )
            }
            Self::Precompile {
                table,
                arg_a,
                arg_b,
                arg_c,
                aux,
            } => {
                write!(f, "{}({arg_a}, {arg_b}, {arg_c}, {aux})", table.name())
            }
        }
    }
}
