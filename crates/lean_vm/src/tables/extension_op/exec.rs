use crate::DIMENSION;
use crate::EF;
use crate::F;
use crate::Memory;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::extension_op::{EXT_OP_LEN_MULTIPLIER, air::*};
use backend::*;
use utils::ToUsize;

#[derive(Clone, Copy, PartialEq)]
enum Op {
    Add,
    Mul,
    PolyEq,
}

fn compute_elem(v_a: EF, v_b: EF, op: Op) -> EF {
    match op {
        Op::Add => v_a + v_b,
        Op::Mul => v_a * v_b,
        // poly_eq: a*b + (1-a)*(1-b)
        Op::PolyEq => (v_a * v_b).double() - v_a - v_b + F::ONE,
    }
}

fn accumulate(elem: EF, comp_tail: EF, op: Op) -> EF {
    match op {
        Op::PolyEq => elem * comp_tail,
        Op::Add | Op::Mul => elem + comp_tail,
    }
}

/// For single-element Add/Mul ops, solve for an unknown operand when the result is known.
/// A op B = C: if A unknown, A = C inv_op B; if B unknown, B = C inv_op A.
fn solve_unknowns(ptr_a: F, ptr_b: F, ptr_res: F, is_be: bool, op: Op, memory: &mut Memory) -> Result<(), RunnerError> {
    let addr_a = ptr_a.to_usize();
    let addr_b = ptr_b.to_usize();
    let addr_res = ptr_res.to_usize();

    let a = if is_be {
        memory.get(addr_a).map(EF::from)
    } else {
        memory.get_ef_element(addr_a)
    };
    let b = memory.get_ef_element(addr_b);
    let c = memory.get_ef_element(addr_res);

    match (a, b, c) {
        (Ok(a), Ok(b), Ok(c)) => {
            if compute_elem(a, b, op) != c {
                return Err(RunnerError::InvalidExtensionOp);
            }
        }
        (Ok(_), Ok(_), Err(_)) => {} // result unknown: compute normally
        (Err(_), Ok(b), Ok(c)) => {
            let a = match op {
                Op::Add => c - b,
                Op::Mul => c / b,
                Op::PolyEq => unreachable!(),
            };
            if is_be {
                memory.set(addr_a, a.as_base().expect("solved A not in base field"))?;
            } else {
                memory.set_ef_element(addr_a, a)?;
            }
        }
        (Ok(a), Err(_), Ok(c)) => {
            let b = match op {
                Op::Add => c - a,
                Op::Mul => c / a,
                Op::PolyEq => unreachable!(),
            };
            memory.set_ef_element(addr_b, b)?;
        }
        _ => return Err(RunnerError::InvalidExtensionOp),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn exec_multi_row(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    is_be: bool,
    op: Op,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    assert!(size >= 1);

    if size == 1 && op != Op::PolyEq {
        solve_unknowns(ptr_a, ptr_b, ptr_res, is_be, op, memory)?;
    }

    let a_stride = if is_be { 1 } else { DIMENSION };

    // 1. Read all operands and compute elem values
    let mut elems = Vec::with_capacity(size);
    let mut v_bs = Vec::with_capacity(size);
    let mut idx_as = Vec::with_capacity(size);
    let mut idx_bs = Vec::with_capacity(size);

    for i in 0..size {
        let addr_a = ptr_a.to_usize() + i * a_stride;
        let addr_b = ptr_b.to_usize() + i * DIMENSION;
        let idx_a_f = F::from_usize(addr_a);
        let idx_b_f = F::from_usize(addr_b);

        let v_a = if is_be {
            EF::from(memory.get(addr_a)?)
        } else {
            memory.get_ef_element(addr_a)?
        };
        let v_b = memory.get_ef_element(addr_b)?;

        elems.push(compute_elem(v_a, v_b, op));
        v_bs.push(v_b);
        idx_as.push(idx_a_f);
        idx_bs.push(idx_b_f);
    }

    // 2. Backward accumulation: compute computation[i] from bottom to top
    let mut computations = vec![EF::ZERO; size];
    computations[size - 1] = elems[size - 1];
    for i in (0..size - 1).rev() {
        computations[i] = accumulate(elems[i], computations[i + 1], op);
    }

    // 3. Write result to memory
    let result = computations[0];
    memory.set_ef_element(ptr_res.to_usize(), result)?;

    // 4. Push trace rows
    let is_be_f = F::from_bool(is_be);
    let flag_add = op == Op::Add;
    let flag_mul = op == Op::Mul;
    let flag_poly_eq = op == Op::PolyEq;
    let flag_add_f = F::from_bool(flag_add);
    let flag_mul_f = F::from_bool(flag_mul);
    let flag_poly_eq_f = F::from_bool(flag_poly_eq);
    let mode_bits = 2 * is_be as usize + 4 * flag_add as usize + 8 * flag_mul as usize + 16 * flag_poly_eq as usize;

    let result_coords = result.as_basis_coefficients_slice();

    for i in 0..size {
        let is_start = i == 0;
        let current_len = size - i;

        trace.base[COL_IS_BE].push(is_be_f);
        trace.base[COL_START].push(F::from_bool(is_start));
        trace.base[COL_FLAG_ADD].push(flag_add_f);
        trace.base[COL_FLAG_MUL].push(flag_mul_f);
        trace.base[COL_FLAG_POLY_EQ].push(flag_poly_eq_f);
        trace.base[COL_LEN].push(F::from_usize(current_len));
        trace.base[COL_IDX_A].push(idx_as[i]);
        trace.base[COL_IDX_B].push(idx_bs[i]);
        trace.base[COL_IDX_RES].push(ptr_res);

        // COL_VA+0..5: filled later by fill_trace_extension_op (push zeros as placeholders)
        for k in 0..DIMENSION {
            trace.base[COL_VA + k].push(F::ZERO);
        }
        for (k, &val) in v_bs[i].as_basis_coefficients_slice().iter().enumerate() {
            trace.base[COL_VB + k].push(val);
        }
        for (k, &val) in result_coords.iter().enumerate() {
            trace.base[COL_VRES + k].push(val);
        }
        for (k, &val) in computations[i].as_basis_coefficients_slice().iter().enumerate() {
            trace.base[COL_COMP + k].push(val);
        }

        // Virtual columns
        trace.base[COL_ACTIVATION_FLAG].push(F::from_bool(is_start));
        trace.base[COL_AUX_EXTENSION_OP].push(F::from_usize(mode_bits + EXT_OP_LEN_MULTIPLIER * current_len));
    }

    Ok(())
}

pub(super) fn exec_add_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, true, Op::Add, memory, trace)
}

pub(super) fn exec_add_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, false, Op::Add, memory, trace)
}

pub(super) fn exec_dot_product_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, true, Op::Mul, memory, trace)
}

pub(super) fn exec_dot_product_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, false, Op::Mul, memory, trace)
}

pub(super) fn exec_poly_eq_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, true, Op::PolyEq, memory, trace)
}

pub(super) fn exec_poly_eq_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, false, Op::PolyEq, memory, trace)
}

/// Fill the VALUE_A columns (5 base field coordinates) after execution
/// by looking up memory at idx_A addresses.
pub fn fill_trace_extension_op(trace: &mut TableTrace, memory: &[F]) {
    let n = trace.base[COL_IDX_A].len();
    for i in 0..n {
        let addr = trace.base[COL_IDX_A][i].to_usize();
        for k in 0..DIMENSION {
            trace.base[COL_VA + k][i] = memory[addr + k];
        }
    }
}
