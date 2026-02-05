use crate::EF;
use crate::F;
use crate::Memory;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::dot_product::*;
use utils::ToUsize;

pub(super) fn exec_dot_product_be(
    ptr_arg_0: F,
    ptr_arg_1: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    assert!(size > 0);

    let slice_0 = memory.get_slice(ptr_arg_0.to_usize(), size)?;
    let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1.to_usize(), size)?;
    let dot_product_result = dot_product::<EF, _, _>(slice_1.iter().copied(), slice_0.iter().copied());

    memory.set_ef_element(ptr_res.to_usize(), dot_product_result)?;

    {
        {
            let computation = &mut trace.ext[DOT_COL_COMPUTATION];
            computation.extend(EF::zero_vec(size));
            let new_size = computation.len();
            computation[new_size - 1] = slice_1[size - 1] * slice_0[size - 1];
            for i in 0..size - 1 {
                computation[new_size - 2 - i] =
                    computation[new_size - 1 - i] + slice_1[size - 2 - i] * slice_0[size - 2 - i];
            }
        }

        trace.base[DOT_COL_IS_BE].extend(std::iter::repeat_n(F::from_bool(true), size));
        trace.base[DOT_COL_FLAG].push(F::ONE);
        trace.base[DOT_COL_FLAG].extend(F::zero_vec(size - 1));
        trace.base[DOT_COL_START].push(F::ONE);
        trace.base[DOT_COL_START].extend(F::zero_vec(size - 1));
        trace.base[DOT_COL_LEN].extend(((1..=size).rev()).map(F::from_usize));
        trace.base[DOT_COL_AUX].extend(((1..=size).rev()).map(|x| F::from_bool(true) + F::from_usize(2 * x)));
        trace.base[DOT_COL_A].extend((0..size).map(|i| F::from_usize(ptr_arg_0.to_usize() + i)));
        trace.base[DOT_COL_B].extend((0..size).map(|i| F::from_usize(ptr_arg_1.to_usize() + i * DIMENSION)));
        trace.base[DOT_COL_RES].extend(vec![F::from_usize(ptr_res.to_usize()); size]);
        trace.ext[DOT_COL_VALUE_B].extend(slice_1);
        trace.ext[DOT_COL_VALUE_RES].extend(vec![dot_product_result; size]);

        // trace.base[COL_VALUE_A_F] and trace.ext[COL_VALUE_A_EF] are filled later
    }

    Ok(())
}

pub(super) fn exec_dot_product_ee(
    ptr_arg_0: F,
    ptr_arg_1: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    assert!(size > 0);

    let (slice_0, slice_1, dot_product_result) = if ptr_arg_1.to_usize() == ONE_VEC_PTR {
        if size != 1 {
            unimplemented!("weird use case");
        }
        if ptr_res.to_usize() == ZERO_VEC_PTR {
            memory.set_ef_element(ptr_arg_0.to_usize(), EF::ZERO)?;
            (vec![EF::ZERO], vec![EF::ONE], EF::ZERO)
        } else {
            let slice_0 = memory.get_continuous_slice_of_ef_elements(ptr_arg_0.to_usize(), size)?;
            let res = slice_0[0];
            memory.set_ef_element(ptr_res.to_usize(), res)?;
            (slice_0, vec![EF::ONE], res)
        }
    } else {
        match (
            memory.get_continuous_slice_of_ef_elements(ptr_arg_0.to_usize(), size),
            memory.get_continuous_slice_of_ef_elements(ptr_arg_1.to_usize(), size),
            memory.get_ef_element(ptr_res.to_usize()),
        ) {
            (Ok(s0), Ok(s1), Ok(res)) => {
                if dot_product::<EF, _, _>(s0.iter().copied(), s1.iter().copied()) != res {
                    return Err(RunnerError::InvalidDotProduct);
                }
                (s0, s1, res)
            }
            (Ok(s0), Ok(s1), Err(_)) => {
                let dot_product_result = dot_product::<EF, _, _>(s0.iter().copied(), s1.iter().copied());
                memory.set_ef_element(ptr_res.to_usize(), dot_product_result)?;
                (s0, s1, dot_product_result)
            }
            (Err(_), Ok(s1), Ok(res)) if size == 1 => {
                let div = res / s1[0];
                memory.set_ef_element(ptr_arg_0.to_usize(), div)?;
                (vec![div], s1, res)
            }
            (Ok(s0), Err(_), Ok(res)) if size == 1 => {
                let div = res / s0[0];
                memory.set_ef_element(ptr_arg_1.to_usize(), div)?;
                (s0, vec![div], res)
            }
            _ => {
                return Err(RunnerError::InvalidDotProduct);
            }
        }
    };

    {
        {
            let computation = &mut trace.ext[DOT_COL_COMPUTATION];
            computation.extend(EF::zero_vec(size));
            let new_size = computation.len();
            computation[new_size - 1] = slice_1[size - 1] * slice_0[size - 1];
            for i in 0..size - 1 {
                computation[new_size - 2 - i] =
                    computation[new_size - 1 - i] + slice_1[size - 2 - i] * slice_0[size - 2 - i];
            }
        }

        trace.base[DOT_COL_IS_BE].extend(std::iter::repeat_n(F::from_bool(false), size));
        trace.base[DOT_COL_FLAG].push(F::ONE);
        trace.base[DOT_COL_FLAG].extend(F::zero_vec(size - 1));
        trace.base[DOT_COL_START].push(F::ONE);
        trace.base[DOT_COL_START].extend(F::zero_vec(size - 1));
        trace.base[DOT_COL_LEN].extend(((1..=size).rev()).map(F::from_usize));
        trace.base[DOT_COL_AUX].extend(((1..=size).rev()).map(|x| F::from_bool(false) + F::from_usize(2 * x)));
        trace.base[DOT_COL_A].extend((0..size).map(|i| F::from_usize(ptr_arg_0.to_usize() + i * DIMENSION)));
        trace.base[DOT_COL_B].extend((0..size).map(|i| F::from_usize(ptr_arg_1.to_usize() + i * DIMENSION)));
        trace.base[DOT_COL_RES].extend(vec![F::from_usize(ptr_res.to_usize()); size]);
        trace.ext[DOT_COL_VALUE_B].extend(slice_1);
        trace.ext[DOT_COL_VALUE_RES].extend(vec![dot_product_result; size]);

        // trace.base[COL_VALUE_A_F] and trace.ext[COL_VALUE_A_EF] are filled later
    }

    Ok(())
}

pub fn fill_trace_dot_product(trace: &mut TableTrace, memory: &[F]) {
    assert!(trace.base[DOT_COL_VALUE_A_F].is_empty());
    assert!(trace.ext[DOT_COL_VALUE_A_EF].is_empty());
    trace.base[DOT_COL_VALUE_A_F] = F::zero_vec(trace.base[DOT_COL_A].len());
    trace.ext[DOT_COL_VALUE_A_EF] = EF::zero_vec(trace.base[DOT_COL_A].len());
    for i in 0..trace.base[DOT_COL_A].len() {
        // TODO parallelize
        let addr = trace.base[DOT_COL_A][i].to_usize();
        let value_f = memory[addr];
        let value_ef = EF::from_basis_coefficients_slice(&memory[addr..][..DIMENSION]).unwrap();
        trace.base[DOT_COL_VALUE_A_F][i] = value_f;
        trace.ext[DOT_COL_VALUE_A_EF][i] = value_ef;
    }
}
