use crate::DIMENSION;
use crate::EF;
use crate::F;
use crate::Memory;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::extension_op::{EXT_OP_LEN_MULTIPLIER, air::*};
use backend::*;
use utils::ToUsize;

/// Compute elem value for a single (v_a, v_b) pair depending on mode.
fn compute_elem(v_a: EF, v_b: EF, flag_add: bool, flag_mul: bool) -> EF {
    if flag_add {
        v_a + v_b
    } else if flag_mul {
        v_a * v_b
    } else {
        // poly_eq: a*b + (1-a)*(1-b)
        (v_a * v_b).double() - v_a - v_b + F::ONE
    }
}

/// Accumulate elem into running computation.
/// For additive modes (ADD, MUL): comp = elem + comp_tail
/// For multiplicative mode (POLY_EQ): comp = elem * comp_tail
fn accumulate(elem: EF, comp_tail: EF, is_poly_eq: bool) -> EF {
    if is_poly_eq { elem * comp_tail } else { elem + comp_tail }
}

/// Execute a multi-row extension_op and push N trace rows (backward accumulation).
///
/// Row ordering: row 0 is the START row (flag=1, len=N, computation=result),
/// row N-1 is the last row (len=1, computation=elem[N-1]).
///
/// For BE mode: arg_A increments by 1 per row (base field elements).
/// For EE mode: arg_A increments by DIMENSION per row (extension field elements).
/// idx_B always increments by DIMENSION per row.
#[allow(clippy::too_many_arguments)]
fn exec_multi_row(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    is_be: bool,
    flag_add: bool,
    flag_mul: bool,
    flag_poly_eq: bool,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    assert!(size >= 1);
    let a_stride = if is_be { 1 } else { DIMENSION };

    // 1. Read all operands and compute elem values
    let mut elems = Vec::with_capacity(size);
    let mut v_a_fs = Vec::with_capacity(size);
    let mut v_bs = Vec::with_capacity(size);
    let mut arg_as = Vec::with_capacity(size);
    let mut idx_bs = Vec::with_capacity(size);

    for i in 0..size {
        let addr_a = ptr_a.to_usize() + i * a_stride;
        let addr_b = ptr_b.to_usize() + i * DIMENSION;
        let arg_a_f = F::from_usize(addr_a);
        let idx_b_f = F::from_usize(addr_b);

        let v_a = if is_be {
            let val_f = memory.get(addr_a)?;
            v_a_fs.push(val_f);
            EF::from(val_f)
        } else {
            let val_ef = memory.get_ef_element(addr_a)?;
            v_a_fs.push(memory.get(addr_a)?);
            val_ef
        };
        let v_b = memory.get_ef_element(addr_b)?;

        let elem = compute_elem(v_a, v_b, flag_add, flag_mul);
        elems.push(elem);
        v_bs.push(v_b);
        arg_as.push(arg_a_f);
        idx_bs.push(idx_b_f);
    }

    // 2. Backward accumulation: compute computation[i] from bottom to top
    let mut computations = vec![EF::ZERO; size];
    computations[size - 1] = elems[size - 1];
    for i in (0..size - 1).rev() {
        computations[i] = accumulate(elems[i], computations[i + 1], flag_poly_eq);
    }

    // 3. Write result to memory
    let result = computations[0];
    memory.set_ef_element(ptr_res.to_usize(), result)?;

    // 4. Push trace rows
    let is_be_f = F::from_bool(is_be);
    let flag_add_f = F::from_bool(flag_add);
    let flag_mul_f = F::from_bool(flag_mul);
    let flag_poly_eq_f = F::from_bool(flag_poly_eq);
    let mode_bits = 2 * is_be as usize + 4 * flag_add as usize + 8 * flag_mul as usize + 16 * flag_poly_eq as usize;

    for i in 0..size {
        let is_start = i == 0;
        let current_len = size - i;

        trace.base[COL_IS_BE].push(is_be_f);
        trace.base[COL_ACTIVATION_FLAG].push(F::from_bool(is_start));
        trace.base[COL_START].push(F::from_bool(is_start));
        trace.base[COL_FLAG_ADD].push(flag_add_f);
        trace.base[COL_FLAG_MUL].push(flag_mul_f);
        trace.base[COL_FLAG_POLY_EQ].push(flag_poly_eq_f);
        trace.base[COL_LEN].push(F::from_usize(current_len));
        trace.base[COL_ARG_A].push(arg_as[i]);
        trace.base[COL_IDX_B].push(idx_bs[i]);
        trace.base[COL_IDX_R].push(ptr_res);
        trace.base[COL_VALUE_A_F].push(v_a_fs[i]);
        trace.base[COL_AUX_EXTENSION_OP].push(F::from_usize(mode_bits + EXT_OP_LEN_MULTIPLIER * current_len));

        // EF columns: v_A_EF is filled later by fill_trace_extension_op
        trace.ext[COL_VALUE_B].push(v_bs[i]);
        trace.ext[COL_VALUE_RES].push(result);
        trace.ext[COL_COMPUTATION].push(computations[i]);
    }

    Ok(())
}

/// Special handling for dot_product_ee: supports solving for unknown operands.
fn exec_dot_product_ee_multi(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    if size == 1 {
        // Single-element: support solving for unknown operands
        match (
            memory.get_ef_element(ptr_a.to_usize()),
            memory.get_ef_element(ptr_b.to_usize()),
            memory.get_ef_element(ptr_res.to_usize()),
        ) {
            (Ok(val_a), Ok(val_b), Ok(res)) => {
                if val_a * val_b != res {
                    return Err(RunnerError::InvalidDotProduct);
                }
            }
            (Ok(_val_a), Ok(_val_b), Err(_)) => {
                // Result unknown: compute normally via exec_multi_row
            }
            (Err(_), Ok(val_b), Ok(res)) => {
                let val_a = res / val_b;
                memory.set_ef_element(ptr_a.to_usize(), val_a)?;
            }
            (Ok(val_a), Err(_), Ok(res)) => {
                let val_b = res / val_a;
                memory.set_ef_element(ptr_b.to_usize(), val_b)?;
            }
            _ => {
                return Err(RunnerError::InvalidDotProduct);
            }
        }
    }
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, false, false, true, false, memory, trace)
}

// ─── Public execution functions ───

pub(super) fn exec_add_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, true, true, false, false, memory, trace)
}

pub(super) fn exec_add_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, false, true, false, false, memory, trace)
}

pub(super) fn exec_dot_product_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, true, false, true, false, memory, trace)
}

pub(super) fn exec_dot_product_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_dot_product_ee_multi(ptr_a, ptr_b, ptr_res, size, memory, trace)
}

pub(super) fn exec_poly_eq_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, true, false, false, true, memory, trace)
}

pub(super) fn exec_poly_eq_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    exec_multi_row(ptr_a, ptr_b, ptr_res, size, false, false, false, true, memory, trace)
}

/// Fill the VALUE_A_EF column after execution by looking up memory at ARG_A addresses.
/// This is done post-execution because the lookup always happens (unconditionally).
pub fn fill_trace_extension_op(trace: &mut TableTrace, memory: &[F]) {
    assert!(trace.ext[COL_VALUE_A_EF].is_empty());
    let n = trace.base[COL_ARG_A].len();
    trace.ext[COL_VALUE_A_EF] = EF::zero_vec(n);
    for i in 0..n {
        let addr = trace.base[COL_ARG_A][i].to_usize();
        let value_ef = EF::from_basis_coefficients_slice(&memory[addr..][..DIMENSION]).unwrap();
        trace.ext[COL_VALUE_A_EF][i] = value_ef;
    }
}
