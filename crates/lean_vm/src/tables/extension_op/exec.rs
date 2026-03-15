use crate::DIMENSION;
use crate::EF;
use crate::ExtensionPrecompileAuxArgs;
use crate::ExtensionPrecompileField;
use crate::ExtensionPrecompileMode;
use crate::F;
use crate::Memory;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::extension_op::air::*;
use crate::tables::{
    EXTENSION_PRECOMPILE_ENCODING_BIT_ADD, EXTENSION_PRECOMPILE_ENCODING_BIT_DOT_PRODUCT,
    EXTENSION_PRECOMPILE_ENCODING_BIT_IS_BE, EXTENSION_PRECOMPILE_ENCODING_BIT_POLY_EQ,
    EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE,
};
use backend::*;
use utils::ToUsize;

fn compute_elem(v_a: EF, v_b: EF, op: ExtensionPrecompileMode) -> EF {
    match op {
        ExtensionPrecompileMode::Add => v_a + v_b,
        ExtensionPrecompileMode::DotProduct => v_a * v_b,
        // poly_eq: a*b + (1-a)*(1-b)
        ExtensionPrecompileMode::PolyEq => (v_a * v_b).double() - v_a - v_b + F::ONE,
    }
}

fn accumulate(elem: EF, comp_tail: EF, op: ExtensionPrecompileMode) -> EF {
    match op {
        ExtensionPrecompileMode::PolyEq => elem * comp_tail,
        ExtensionPrecompileMode::Add | ExtensionPrecompileMode::DotProduct => elem + comp_tail,
    }
}

/// For single-element Add/Mul ops, solve for an unknown operand when the result is known.
/// A op B = C: if A unknown, A = C inv_op B; if B unknown, B = C inv_op A.
fn solve_unknowns(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    aux_args: &ExtensionPrecompileAuxArgs,
    memory: &mut Memory,
) -> Result<(), RunnerError> {
    let addr_a = ptr_a.to_usize();
    let addr_b = ptr_b.to_usize();
    let addr_res = ptr_res.to_usize();

    let a = match aux_args.field {
        ExtensionPrecompileField::BE => memory.get(addr_a).map(EF::from),
        ExtensionPrecompileField::EE => memory.get_ef_element(addr_a),
    };
    let b = memory.get_ef_element(addr_b);
    let c = memory.get_ef_element(addr_res);

    match (a, b, c) {
        (Ok(a), Ok(b), Ok(c)) => {
            if compute_elem(a, b, aux_args.op) != c {
                return Err(RunnerError::InvalidExtensionOp);
            }
        }
        (Ok(_), Ok(_), Err(_)) => {} // result unknown: compute normally
        (Err(_), Ok(b), Ok(c)) => {
            let a = match aux_args.op {
                ExtensionPrecompileMode::Add => c - b,
                ExtensionPrecompileMode::DotProduct => c / b,
                ExtensionPrecompileMode::PolyEq => unreachable!(),
            };
            match aux_args.field {
                ExtensionPrecompileField::BE => {
                    memory.set(addr_a, a.as_base().expect("solved A not in base field"))?;
                }
                ExtensionPrecompileField::EE => {
                    memory.set_ef_element(addr_a, a)?;
                }
            }
        }
        (Ok(a), Err(_), Ok(c)) => {
            let b = match aux_args.op {
                ExtensionPrecompileMode::Add => c - a,
                ExtensionPrecompileMode::DotProduct => c / a,
                ExtensionPrecompileMode::PolyEq => unreachable!(),
            };
            memory.set_ef_element(addr_b, b)?;
        }
        _ => return Err(RunnerError::InvalidExtensionOp),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn exec_multi_row(
    ptr_a: F,
    ptr_b: F,
    ptr_res: F,
    aux_args: &ExtensionPrecompileAuxArgs,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    let size = aux_args.size;
    assert!(size >= 1);

    if size == 1 && aux_args.op != ExtensionPrecompileMode::PolyEq {
        solve_unknowns(ptr_a, ptr_b, ptr_res, aux_args, memory)?;
    }

    let a_stride = match aux_args.field {
        ExtensionPrecompileField::BE => 1,
        ExtensionPrecompileField::EE => DIMENSION,
    };

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

        let v_a = match aux_args.field {
            ExtensionPrecompileField::BE => EF::from(memory.get(addr_a)?),
            ExtensionPrecompileField::EE => memory.get_ef_element(addr_a)?,
        };
        let v_b = memory.get_ef_element(addr_b)?;

        elems.push(compute_elem(v_a, v_b, aux_args.op));
        v_bs.push(v_b);
        idx_as.push(idx_a_f);
        idx_bs.push(idx_b_f);
    }

    // 2. Backward accumulation: compute computation[i] from bottom to top
    let mut computations = vec![EF::ZERO; size];
    computations[size - 1] = elems[size - 1];
    for i in (0..size - 1).rev() {
        computations[i] = accumulate(elems[i], computations[i + 1], aux_args.op);
    }

    // 3. Write result to memory
    let result = computations[0];
    memory.set_ef_element(ptr_res.to_usize(), result)?;

    // 4. Push trace rows
    let is_be = aux_args.field == ExtensionPrecompileField::BE;
    let is_be_f = F::from_bool(is_be);
    let flag_add = aux_args.op == ExtensionPrecompileMode::Add;
    let flag_mul = aux_args.op == ExtensionPrecompileMode::DotProduct;
    let flag_poly_eq = aux_args.op == ExtensionPrecompileMode::PolyEq;
    let flag_add_f = F::from_bool(flag_add);
    let flag_mul_f = F::from_bool(flag_mul);
    let flag_poly_eq_f = F::from_bool(flag_poly_eq);
    let mode_bits = (is_be as usize) << EXTENSION_PRECOMPILE_ENCODING_BIT_IS_BE
        | (flag_add as usize) << EXTENSION_PRECOMPILE_ENCODING_BIT_ADD
        | (flag_mul as usize) << EXTENSION_PRECOMPILE_ENCODING_BIT_DOT_PRODUCT
        | (flag_poly_eq as usize) << EXTENSION_PRECOMPILE_ENCODING_BIT_POLY_EQ;

    let result_coords = result.as_basis_coefficients_slice();

    for i in 0..size {
        let is_start = i == 0;
        let current_len = size - i;

        trace.base[COL_IS_BE].push(is_be_f);
        trace.base[COL_START].push(F::from_bool(is_start));
        trace.base[COL_FLAG_ADD].push(flag_add_f);
        trace.base[COL_FLAG_DOT_PRODUCT].push(flag_mul_f);
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
        trace.base[COL_AUX_EXTENSION_OP].push(F::from_usize(
            mode_bits + (current_len << EXTENSION_PRECOMPILE_ENCODING_BIT_SIZE),
        ));
    }

    Ok(())
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
