use crate::EF;
use crate::F;
use crate::Memory;
use crate::RunnerError;
use crate::TableTrace;
use crate::tables::eq_poly_base_ext::*;
use utils::ToUsize;

pub(super) fn exec_eq_poly_base_ext(
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

    let computation = &mut trace.ext[COL_COMPUTATION];
    computation.extend(EF::zero_vec(size));
    let new_size = computation.len();
    computation[new_size - 1] =
        slice_1[size - 1] * slice_0[size - 1] + (EF::ONE - slice_1[size - 1]) * (F::ONE - slice_0[size - 1]);
    for i in 0..size - 1 {
        computation[new_size - 2 - i] = computation[new_size - 1 - i]
            * (slice_1[size - 2 - i] * slice_0[size - 2 - i]
                + (EF::ONE - slice_1[size - 2 - i]) * (F::ONE - slice_0[size - 2 - i]));
    }
    let final_result = computation[new_size - size];
    memory.set_ef_element(ptr_res.to_usize(), final_result)?;

    trace.base[COL_FLAG].push(F::ONE);
    trace.base[COL_FLAG].extend(F::zero_vec(size - 1));
    trace.base[COL_LEN].extend(((1..=size).rev()).map(F::from_usize));
    trace.base[COL_INDEX_A].extend((0..size).map(|i| F::from_usize(ptr_arg_0.to_usize() + i)));
    trace.base[COL_INDEX_B].extend((0..size).map(|i| F::from_usize(ptr_arg_1.to_usize() + i * DIMENSION)));
    trace.base[COL_INDEX_RES].extend(vec![F::from_usize(ptr_res.to_usize()); size]);
    trace.base[COL_VALUE_A].extend(slice_0);
    trace.ext[COL_VALUE_B].extend(slice_1);
    trace.ext[COL_VALUE_RES].extend(vec![final_result; size]);

    Ok(())
}
