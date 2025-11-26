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

    let slice_0 = memory.slice(ptr_arg_0.to_usize(), size)?;
    let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1.to_usize(), size)?;
    let dot_product_result = dot_product::<EF, _, _>(slice_1.iter().copied(), slice_0.iter().copied());

    memory.set_ef_element(ptr_res.to_usize(), dot_product_result)?;

    {
        {
            let computation = &mut trace.ext[COL_COMPUTATION];
            computation.extend(EF::zero_vec(size));
            let new_size = computation.len();
            computation[new_size - 1] = slice_1[size - 1] * slice_0[size - 1];
            for i in 0..size - 1 {
                computation[new_size - 2 - i] =
                    computation[new_size - 1 - i] + slice_1[size - 2 - i] * slice_0[size - 2 - i];
            }
        }

        trace.base[COL_FLAG].push(F::ONE);
        trace.base[COL_FLAG].extend(F::zero_vec(size - 1));
        trace.base[COL_LEN].extend(((1..=size).rev()).map(F::from_usize));
        trace.base[COL_INDEX_A].extend((0..size).map(|i| F::from_usize(ptr_arg_0.to_usize() + i)));
        trace.base[COL_INDEX_B]
            .extend((0..size).map(|i| F::from_usize(ptr_arg_1.to_usize() + i * DIMENSION)));
        trace.base[COL_INDEX_RES].extend(vec![F::from_usize(ptr_res.to_usize()); size]);
        trace.base[dot_product_air_col_value_a(true)].extend(slice_0);
        trace.ext[COL_VALUE_B].extend(slice_1);
        trace.ext[COL_VALUE_RES].extend(vec![dot_product_result; size]);
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

    let slice_0 = memory.get_continuous_slice_of_ef_elements(ptr_arg_0.to_usize(), size)?;

    let (slice_1, dot_product_result) = if ptr_arg_1.to_usize() == ONE_VEC_PTR * VECTOR_LEN {
        if size != 1 {
            unimplemented!("weird use case");
        }
        (vec![EF::ONE], slice_0[0])
    } else {
        let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1.to_usize(), size)?;
        let dot_product_result = dot_product::<EF, _, _>(slice_1.iter().copied(), slice_0.iter().copied());
        (slice_1, dot_product_result)
    };

    memory.set_ef_element(ptr_res.to_usize(), dot_product_result)?;

    {
        {
            let computation = &mut trace.ext[COL_COMPUTATION];
            computation.extend(EF::zero_vec(size));
            let new_size = computation.len();
            computation[new_size - 1] = slice_1[size - 1] * slice_0[size - 1];
            for i in 0..size - 1 {
                computation[new_size - 2 - i] =
                    computation[new_size - 1 - i] + slice_1[size - 2 - i] * slice_0[size - 2 - i];
            }
        }

        trace.base[COL_FLAG].push(F::ONE);
        trace.base[COL_FLAG].extend(F::zero_vec(size - 1));
        trace.base[COL_LEN].extend(((1..=size).rev()).map(F::from_usize));
        trace.base[COL_INDEX_A]
            .extend((0..size).map(|i| F::from_usize(ptr_arg_0.to_usize() + i * DIMENSION)));
        trace.base[COL_INDEX_B]
            .extend((0..size).map(|i| F::from_usize(ptr_arg_1.to_usize() + i * DIMENSION)));
        trace.base[COL_INDEX_RES].extend(vec![F::from_usize(ptr_res.to_usize()); size]);
        trace.ext[dot_product_air_col_value_a(false)].extend(slice_0);
        trace.ext[COL_VALUE_B].extend(slice_1);
        trace.ext[COL_VALUE_RES].extend(vec![dot_product_result; size]);
    }

    Ok(())
}
