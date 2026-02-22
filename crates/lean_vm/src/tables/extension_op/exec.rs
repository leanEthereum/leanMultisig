use crate::DIMENSION;
use crate::EF;
use crate::F;
use crate::Memory;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::extension_op::air::*;
use backend::*;
use utils::ToUsize;

/// Helper to append a single trace row for an extension_op.
/// `arg_a` is ALWAYS a memory address (pointer). In BE mode, `value_a_f = m[arg_a]`.
fn push_trace_row(
    trace: &mut TableTrace,
    is_be: bool,
    flag_add: bool,
    flag_mul: bool,
    flag_poly_eq: bool,
    arg_a: F,
    idx_b: F,
    idx_r: F,
    value_a_f: F,
    value_b: EF,
    result: EF,
) {
    let is_be_f = F::from_bool(is_be);
    let flag_add_f = F::from_bool(flag_add);
    let flag_mul_f = F::from_bool(flag_mul);
    let flag_poly_eq_f = F::from_bool(flag_poly_eq);

    trace.base[EXT_COL_IS_BE].push(is_be_f);
    trace.base[EXT_COL_FLAG].push(F::ONE);
    trace.base[EXT_COL_FLAG_ADD].push(flag_add_f);
    trace.base[EXT_COL_FLAG_MUL].push(flag_mul_f);
    trace.base[EXT_COL_FLAG_POLY_EQ].push(flag_poly_eq_f);
    trace.base[EXT_COL_ARG_A].push(arg_a);
    trace.base[EXT_COL_IDX_B].push(idx_b);
    trace.base[EXT_COL_IDX_R].push(idx_r);
    trace.base[EXT_COL_VALUE_A_F].push(value_a_f);
    // aux = 2*is_be + 4*flag_add + 8*flag_mul + 16*flag_poly_eq
    let aux_val = 2 * is_be as usize + 4 * flag_add as usize + 8 * flag_mul as usize + 16 * flag_poly_eq as usize;
    trace.base[EXT_COL_AUX].push(F::from_usize(aux_val));

    // EF columns: v_A_EF is filled later by fill_trace_extension_op
    trace.ext[EXT_COL_VALUE_B].push(value_b);
    trace.ext[EXT_COL_VALUE_RES].push(result);
}

// ─── BE mode: arg_a is a POINTER to a single base field element ───

pub(super) fn exec_add_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    let val_a_f = memory.get(ptr_a.to_usize())?;
    let val_b = memory.get_ef_element(ptr_b.to_usize())?;
    let result = EF::from(val_a_f) + val_b;
    memory.set_ef_element(ptr_res.to_usize(), result)?;
    push_trace_row(
        trace, true, true, false, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, result,
    );
    Ok(())
}

pub(super) fn exec_mul_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    let val_a_f = memory.get(ptr_a.to_usize())?;
    let val_b = memory.get_ef_element(ptr_b.to_usize())?;
    let result = EF::from(val_a_f) * val_b;
    memory.set_ef_element(ptr_res.to_usize(), result)?;
    push_trace_row(
        trace, true, false, true, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, result,
    );
    Ok(())
}

pub(super) fn exec_poly_eq_be(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    let val_a_f = memory.get(ptr_a.to_usize())?;
    let val_b = memory.get_ef_element(ptr_b.to_usize())?;
    let val_a = EF::from(val_a_f);
    // poly_eq(a, b) = a*b + (1-a)*(1-b)
    let result = val_a * val_b + (EF::ONE - val_a) * (EF::ONE - val_b);
    memory.set_ef_element(ptr_res.to_usize(), result)?;
    push_trace_row(
        trace, true, false, false, true, ptr_a, ptr_b, ptr_res, val_a_f, val_b, result,
    );
    Ok(())
}

// ─── EE mode: arg_a is a pointer to EF element in memory ───

pub(super) fn exec_add_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    let val_a = memory.get_ef_element(ptr_a.to_usize())?;
    let val_b = memory.get_ef_element(ptr_b.to_usize())?;
    let val_a_f = memory.get(ptr_a.to_usize())?;
    let result = val_a + val_b;
    memory.set_ef_element(ptr_res.to_usize(), result)?;
    push_trace_row(
        trace, false, true, false, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, result,
    );
    Ok(())
}

pub(super) fn exec_mul_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    match (
        memory.get_ef_element(ptr_a.to_usize()),
        memory.get_ef_element(ptr_b.to_usize()),
        memory.get_ef_element(ptr_res.to_usize()),
    ) {
        (Ok(val_a), Ok(val_b), Ok(res)) => {
            if val_a * val_b != res {
                return Err(RunnerError::InvalidDotProduct);
            }
            let val_a_f = memory.get(ptr_a.to_usize())?;
            push_trace_row(
                trace, false, false, true, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, res,
            );
        }
        (Ok(val_a), Ok(val_b), Err(_)) => {
            let result = val_a * val_b;
            memory.set_ef_element(ptr_res.to_usize(), result)?;
            let val_a_f = memory.get(ptr_a.to_usize())?;
            push_trace_row(
                trace, false, false, true, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, result,
            );
        }
        (Err(_), Ok(val_b), Ok(res)) => {
            let val_a = res / val_b;
            memory.set_ef_element(ptr_a.to_usize(), val_a)?;
            let val_a_f = memory.get(ptr_a.to_usize())?;
            push_trace_row(
                trace, false, false, true, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, res,
            );
        }
        (Ok(val_a), Err(_), Ok(res)) => {
            let val_b = res / val_a;
            memory.set_ef_element(ptr_b.to_usize(), val_b)?;
            let val_a_f = memory.get(ptr_a.to_usize())?;
            push_trace_row(
                trace, false, false, true, false, ptr_a, ptr_b, ptr_res, val_a_f, val_b, res,
            );
        }
        _ => {
            return Err(RunnerError::InvalidDotProduct);
        }
    }
    Ok(())
}

pub(super) fn exec_poly_eq_ee(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    let val_a = memory.get_ef_element(ptr_a.to_usize())?;
    let val_b = memory.get_ef_element(ptr_b.to_usize())?;
    let val_a_f = memory.get(ptr_a.to_usize())?;
    // poly_eq(a, b) = a*b + (1-a)*(1-b)
    let result = val_a * val_b + (EF::ONE - val_a) * (EF::ONE - val_b);
    memory.set_ef_element(ptr_res.to_usize(), result)?;
    push_trace_row(
        trace, false, false, false, true, ptr_a, ptr_b, ptr_res, val_a_f, val_b, result,
    );
    Ok(())
}

/// Fill the VALUE_A_EF column after execution by looking up memory at ARG_A addresses.
/// This is done post-execution because the lookup always happens (unconditionally).
pub fn fill_trace_extension_op(trace: &mut TableTrace, memory: &[F]) {
    assert!(trace.ext[EXT_COL_VALUE_A_EF].is_empty());
    let n = trace.base[EXT_COL_ARG_A].len();
    trace.ext[EXT_COL_VALUE_A_EF] = EF::zero_vec(n);
    for i in 0..n {
        let addr = trace.base[EXT_COL_ARG_A][i].to_usize();
        let value_ef = EF::from_basis_coefficients_slice(&memory[addr..][..DIMENSION]).unwrap();
        trace.ext[EXT_COL_VALUE_A_EF][i] = value_ef;
    }
}
