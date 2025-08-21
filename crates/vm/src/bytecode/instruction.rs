use std::{
    fmt,
    fmt::{Display, Formatter},
};

use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, dot_product};
use p3_symmetric::Permutation;
use utils::{Poseidon16, Poseidon24, ToUsize};
use whir_p3::poly::{evals::EvaluationsList, multilinear::MultilinearPoint};

use super::{MemOrConstant, MemOrFp, MemOrFpOrConstant, Operation};
use crate::{DIMENSION, EF, F, Memory, RunnerError};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction {
    // 3 basic instructions
    Computation {
        operation: Operation,
        arg_a: MemOrConstant,
        arg_c: MemOrFp,
        res: MemOrConstant,
    },
    Deref {
        shift_0: usize,
        shift_1: usize,
        res: MemOrFpOrConstant,
    }, // res = m[m[fp + shift_0] + shift_1]
    JumpIfNotZero {
        condition: MemOrConstant,
        dest: MemOrConstant,
        updated_fp: MemOrFp,
    },
    // 4 precompiles:
    Poseidon2_16 {
        arg_a: MemOrConstant, // vectorized pointer, of size 1
        arg_b: MemOrConstant, // vectorized pointer, of size 1
        res: MemOrFp, // vectorized pointer, of size 2 (The Fp would never be used in practice)
    },
    Poseidon2_24 {
        arg_a: MemOrConstant, // vectorized pointer, of size 2 (2 first inputs)
        arg_b: MemOrConstant, // vectorized pointer, of size 1 (3rd = last input)
        res: MemOrFp, // vectorized pointer, of size 1 (3rd = last output) (The Fp would never be used in practice)
    },
    DotProductExtensionExtension {
        arg0: MemOrConstant, // vectorized pointer
        arg1: MemOrConstant, // vectorized pointer
        res: MemOrFp,        // vectorized pointer, of size 1 (never Fp in practice)
        size: usize,
    },
    MultilinearEval {
        coeffs: MemOrConstant, // vectorized pointer, chunk size = 2^n_vars
        point: MemOrConstant,  // vectorized pointer, of size `n_vars`
        res: MemOrFp,          // vectorized pointer, of size 1 (never fp in practice)
        n_vars: usize,
    },
}

impl Instruction {
    pub fn execute(
        &self,
        memory: &mut Memory,
        fp: &mut usize,
        pc: &mut usize,
        p16: &Poseidon16,
        p24: &Poseidon24,
        poseidon16_calls: &mut usize,
        poseidon24_calls: &mut usize,
        dot_ext_ext_calls: &mut usize,
        dot_base_ext_calls: &mut usize,
    ) -> Result<(), RunnerError> {
        match self {
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                if res.is_value_unknown(memory, *fp) {
                    let addr = res.memory_address(*fp)?;
                    let a = arg_a.read_value(memory, *fp)?;
                    let b = arg_c.read_value(memory, *fp)?;
                    memory.set(addr, operation.compute(a, b))?;
                } else if arg_a.is_value_unknown(memory, *fp) {
                    let addr = arg_a.memory_address(*fp)?;
                    let r = res.read_value(memory, *fp)?;
                    let b = arg_c.read_value(memory, *fp)?;
                    let a = operation
                        .inverse_compute(r, b)
                        .ok_or(RunnerError::DivByZero)?;
                    memory.set(addr, a)?;
                } else if arg_c.is_value_unknown(memory, *fp) {
                    let addr = arg_c.memory_address(*fp)?;
                    let r = res.read_value(memory, *fp)?;
                    let a = arg_a.read_value(memory, *fp)?;
                    let b = operation
                        .inverse_compute(r, a)
                        .ok_or(RunnerError::DivByZero)?;
                    memory.set(addr, b)?;
                } else {
                    let a = arg_a.read_value(memory, *fp)?;
                    let b = arg_c.read_value(memory, *fp)?;
                    let r = res.read_value(memory, *fp)?;
                    let c = operation.compute(a, b);
                    if r != c {
                        return Err(RunnerError::NotEqual(c, r));
                    }
                }
                *pc += 1;
            }

            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => {
                let ptr = memory.get(*fp + *shift_0)?.to_usize();
                if res.is_value_unknown(memory, *fp) {
                    let addr_res = res.memory_address(*fp)?;
                    let v = memory.get(ptr + *shift_1)?;
                    memory.set(addr_res, v)?;
                } else {
                    let v = res.read_value(memory, *fp)?;
                    memory.set(ptr + *shift_1, v)?;
                }
                *pc += 1;
            }

            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                let c = condition.read_value(memory, *fp)?;
                assert!([F::ZERO, F::ONE].contains(&c));
                if c == F::ZERO {
                    *pc += 1;
                } else {
                    *pc = dest.read_value(memory, *fp)?.to_usize();
                    *fp = updated_fp.read_value(memory, *fp)?.to_usize();
                }
            }

            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                *poseidon16_calls += 1;

                let a_ptr = arg_a.read_value(memory, *fp)?.to_usize();
                let b_ptr = arg_b.read_value(memory, *fp)?.to_usize();
                let r_ptr = res.read_value(memory, *fp)?.to_usize();

                let a = memory.get_vector(a_ptr)?;
                let b = memory.get_vector(b_ptr)?;

                let mut state = [F::ZERO; DIMENSION * 2];
                state[..DIMENSION].copy_from_slice(&a);
                state[DIMENSION..].copy_from_slice(&b);
                p16.permute_mut(&mut state);

                memory.set_vectorized_slice(r_ptr, &state)?;
                *pc += 1;
            }

            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                *poseidon24_calls += 1;

                let a_ptr = arg_a.read_value(memory, *fp)?.to_usize();
                let b_ptr = arg_b.read_value(memory, *fp)?.to_usize();
                let r_ptr = res.read_value(memory, *fp)?.to_usize();

                let a0 = memory.get_vector(a_ptr)?;
                let a1 = memory.get_vector(a_ptr + 1)?;
                let b = memory.get_vector(b_ptr)?;

                let mut state = [F::ZERO; DIMENSION * 3];
                state[..DIMENSION].copy_from_slice(&a0);
                state[DIMENSION..2 * DIMENSION].copy_from_slice(&a1);
                state[2 * DIMENSION..].copy_from_slice(&b);
                p24.permute_mut(&mut state);

                memory.set_vectorized_slice(r_ptr, &state[2 * DIMENSION..])?;
                *pc += 1;
            }

            Self::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                *dot_ext_ext_calls += 1;

                let p0 = arg0.read_value(memory, *fp)?.to_usize();
                let p1 = arg1.read_value(memory, *fp)?.to_usize();
                let pr = res.read_value(memory, *fp)?.to_usize();

                let s0 = memory.get_vectorized_slice_extension::<EF>(p0, *size)?;
                let s1 = memory.get_vectorized_slice_extension::<EF>(p1, *size)?;

                let dp: [F; DIMENSION] = dot_product::<EF, _, _>(s0.into_iter(), s1.into_iter())
                    .as_basis_coefficients_slice()
                    .try_into()
                    .unwrap();
                memory.set_vector(pr, dp)?;
                *pc += 1;
            }

            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                *dot_base_ext_calls += 1;

                let pcf = coeffs.read_value(memory, *fp)?.to_usize();
                let ppt = point.read_value(memory, *fp)?.to_usize();
                let pr = res.read_value(memory, *fp)?.to_usize();

                let start = pcf << *n_vars;
                let len = 1usize << *n_vars;
                let coeffs = memory.slice(start, len)?;
                let point = memory.get_vectorized_slice_extension::<EF>(ppt, *n_vars)?;

                let eval = coeffs.evaluate(&MultilinearPoint(point));
                let out: [F; DIMENSION] = eval.as_basis_coefficients_slice().try_into().unwrap();
                memory.set_vector(pr, out)?;
                *pc += 1;
            }
        }
        Ok(())
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                write!(
                    f,
                    "if {condition} != 0 jump to {dest} with next(fp) = {updated_fp}"
                )
            }
            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_16({arg_a}, {arg_b})")
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                write!(f, "{res} = poseidon2_24({arg_a}, {arg_b})")
            }
        }
    }
}
