//! VM instruction definitions

use super::Operation;
use super::operands::{MemOrConstant, MemOrFp, MemOrFpOrConstant};
use crate::core::{DIMENSION, EF, F, Label, VECTOR_LEN};
use crate::diagnostics::RunnerError;
use crate::execution::Memory;
use crate::witness::{
    RowMultilinearEval, WitnessDotProduct, WitnessMultilinearEval, WitnessPoseidon16,
    WitnessPoseidon24,
};
use multilinear_toolkit::prelude::*;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, dot_product};
use p3_symmetric::Permutation;
use p3_util::log2_ceil_usize;
use std::fmt::{Display, Formatter};
use utils::{ToUsize, get_poseidon16, get_poseidon24};

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

    /// Poseidon2 cryptographic hash with 16-element input
    Poseidon2_16 {
        /// First input vector (vectorized pointer, size 1)
        arg_a: MemOrConstant,
        /// Second input vector (vectorized pointer, size 1)
        arg_b: MemOrConstant,
        /// Output hash result (vectorized pointer, size 1 or 2 depending on compression)
        res: MemOrFp,
        /// Whether to perform compression (output size 1) or not (output size 2)
        is_compression: bool,
    },

    /// Poseidon2 cryptographic hash with 24-element input
    Poseidon2_24 {
        /// First input vector (vectorized pointer, size 2)
        arg_a: MemOrConstant,
        /// Second input vector (vectorized pointer, size 1)
        arg_b: MemOrConstant,
        /// Output hash result (vectorized pointer, size 1)
        res: MemOrFp,
    },

    /// Dot product computation between extension field element vectors
    DotProductExtensionExtension {
        /// First vector pointer (normal pointer, size `size`)
        arg0: MemOrConstant,
        /// Second vector pointer (normal pointer, size `size`)
        arg1: MemOrConstant,
        /// Result destination (normal pointer, size 1)
        res: MemOrFp,
        /// Vector length for the dot product
        size: usize,
    },

    /// Multilinear polynomial evaluation instruction
    MultilinearEval {
        /// Polynomial coefficients (vectorized pointer, chunk size = 2^n_vars)
        coeffs: MemOrConstant,
        /// Evaluation point (normal pointer to `n_vars` continuous EF elements)
        point: MemOrConstant,
        /// Evaluation result (vectorized pointer to 1 EF element)
        res: MemOrFp,
        /// Number of variables in the multilinear polynomial
        n_vars: usize,
    },
}

/// Execution context for instruction processing
#[derive(Debug)]
pub struct InstructionContext<'a> {
    pub memory: &'a mut Memory,
    pub fp: &'a mut usize,
    pub pc: &'a mut usize,
    pub pcs: &'a Vec<usize>,
    pub poseidons_16: &'a mut Vec<WitnessPoseidon16>,
    pub poseidons_24: &'a mut Vec<WitnessPoseidon24>,
    pub dot_products: &'a mut Vec<WitnessDotProduct>,
    pub multilinear_evals: &'a mut Vec<WitnessMultilinearEval>,
    pub add_counts: &'a mut usize,
    pub mul_counts: &'a mut usize,
    pub deref_counts: &'a mut usize,
    pub jump_counts: &'a mut usize,
}

impl Instruction {
    /// Execute this instruction within the given execution context
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
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => {
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
            Self::Poseidon2_16 {
                arg_a,
                arg_b,
                res,
                is_compression,
            } => {
                let poseidon_16 = get_poseidon16();

                let a_value = arg_a.read_value(ctx.memory, *ctx.fp)?;
                let b_value = arg_b.read_value(ctx.memory, *ctx.fp)?;
                let res_value = res.read_value(ctx.memory, *ctx.fp)?;

                let arg0 = ctx.memory.get_vector(a_value.to_usize())?;
                let arg1 = ctx.memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; VECTOR_LEN * 2];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..].copy_from_slice(&arg1);

                // Keep a copy of the input before permutation for event recording
                let input_before = input;
                poseidon_16.permute_mut(&mut input);

                let res0: [F; VECTOR_LEN] = input[..VECTOR_LEN].try_into().unwrap();
                let res1: [F; VECTOR_LEN] = input[VECTOR_LEN..].try_into().unwrap();

                ctx.memory.set_vector(res_value.to_usize(), res0)?;
                if !is_compression {
                    ctx.memory.set_vector(1 + res_value.to_usize(), res1)?;
                }

                {
                    let cycle = ctx.pcs.len() - 1;
                    let addr_input_a = a_value.to_usize();
                    let addr_input_b = b_value.to_usize();
                    let addr_output = res_value.to_usize();
                    ctx.poseidons_16.push(WitnessPoseidon16 {
                        cycle: Some(cycle),
                        addr_input_a,
                        addr_input_b,
                        addr_output,
                        input: input_before,
                        is_compression: *is_compression,
                    });
                }

                *ctx.pc += 1;
                Ok(())
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                let poseidon_24 = get_poseidon24();

                let a_value = arg_a.read_value(ctx.memory, *ctx.fp)?;
                let b_value = arg_b.read_value(ctx.memory, *ctx.fp)?;
                let res_value = res.read_value(ctx.memory, *ctx.fp)?;

                let arg0 = ctx.memory.get_vector(a_value.to_usize())?;
                let arg1 = ctx.memory.get_vector(1 + a_value.to_usize())?;
                let arg2 = ctx.memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; VECTOR_LEN * 3];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
                input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

                // Keep a copy of the input before permutation for event recording
                let input_before = input;
                poseidon_24.permute_mut(&mut input);

                let res: [F; VECTOR_LEN] = input[2 * VECTOR_LEN..].try_into().unwrap();

                ctx.memory.set_vector(res_value.to_usize(), res)?;

                {
                    let cycle = ctx.pcs.len() - 1;
                    let addr_input_a = a_value.to_usize();
                    let addr_input_b = b_value.to_usize();
                    let addr_output = res_value.to_usize();
                    ctx.poseidons_24.push(WitnessPoseidon24 {
                        cycle: Some(cycle),
                        addr_input_a,
                        addr_input_b,
                        addr_output,
                        input: input_before,
                    });
                }

                *ctx.pc += 1;
                Ok(())
            }
            Self::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                let ptr_arg_0 = arg0.read_value(ctx.memory, *ctx.fp)?.to_usize();
                let ptr_arg_1 = arg1.read_value(ctx.memory, *ctx.fp)?.to_usize();
                let ptr_res = res.read_value(ctx.memory, *ctx.fp)?.to_usize();

                let slice_0 = ctx
                    .memory
                    .get_continuous_slice_of_ef_elements(ptr_arg_0, *size)?;
                let slice_1 = ctx
                    .memory
                    .get_continuous_slice_of_ef_elements(ptr_arg_1, *size)?;

                let dot_product_result =
                    dot_product::<EF, _, _>(slice_0.iter().copied(), slice_1.iter().copied());
                ctx.memory.set_ef_element(ptr_res, dot_product_result)?;

                {
                    let cycle = ctx.pcs.len() - 1;
                    ctx.dot_products.push(WitnessDotProduct {
                        cycle,
                        addr_0: ptr_arg_0,
                        addr_1: ptr_arg_1,
                        addr_res: ptr_res,
                        len: *size,
                        slice_0: slice_0.clone(),
                        slice_1: slice_1.clone(),
                        res: dot_product_result,
                    });
                }

                *ctx.pc += 1;
                Ok(())
            }
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                let ptr_coeffs = coeffs.read_value(ctx.memory, *ctx.fp)?.to_usize();
                let ptr_point = point.read_value(ctx.memory, *ctx.fp)?.to_usize();
                let ptr_res = res.read_value(ctx.memory, *ctx.fp)?.to_usize();
                let n_coeffs = 1 << *n_vars;
                let slice_coeffs = ctx.memory.slice(ptr_coeffs << *n_vars, n_coeffs)?;

                let log_point_size = log2_ceil_usize(*n_vars * DIMENSION);
                let point_slice = ctx
                    .memory
                    .slice(ptr_point << log_point_size, *n_vars * DIMENSION)?;
                for i in *n_vars * DIMENSION..(*n_vars * DIMENSION).next_power_of_two() {
                    ctx.memory.set((ptr_point << log_point_size) + i, F::ZERO)?; // padding
                }
                let point = point_slice[..*n_vars * DIMENSION]
                    .chunks_exact(DIMENSION)
                    .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
                    .collect::<Vec<_>>();

                let eval = slice_coeffs.evaluate(&MultilinearPoint(point.clone()));
                let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
                res_vec.resize(VECTOR_LEN, F::ZERO);
                ctx.memory
                    .set_vector(ptr_res, res_vec.try_into().unwrap())?;

                {
                    let cycle = ctx.pcs.len() - 1;
                    ctx.multilinear_evals.push(WitnessMultilinearEval {
                        cycle,
                        inner: RowMultilinearEval {
                            addr_coeffs: ptr_coeffs,
                            addr_point: ptr_point,
                            addr_res: ptr_res,
                            point,
                            res: eval,
                        },
                    });
                }

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
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => {
                write!(f, "{res} = m[m[fp + {shift_0}] + {shift_1}]")
            }
            Self::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                write!(f, "dot_product({arg0}, {arg1}, {res}, {size})")
            }
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                write!(f, "multilinear_eval({coeffs}, {point}, {res}, {n_vars})")
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
            Self::Poseidon2_16 {
                arg_a,
                arg_b,
                res,
                is_compression,
            } => {
                write!(
                    f,
                    "{res} = poseidon2_16({arg_a}, {arg_b}, compression={is_compression})"
                )
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_24({arg_a}, {arg_b})")
            }
        }
    }
}
