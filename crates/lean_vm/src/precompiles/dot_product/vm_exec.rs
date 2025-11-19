use crate::EF;
use crate::F;
use crate::Memory;
use crate::ONE_VEC_PTR;
use crate::RunnerError;
use crate::VECTOR_LEN;
use crate::WitnessDotProduct;
use multilinear_toolkit::prelude::*;
use utils::ToUsize;

pub(crate) fn exec_dot_product(
    ptr_arg_0: F,
    ptr_arg_1: F,
    ptr_res: F,
    size: usize,
    memory: &mut Memory,
) -> Result<WitnessDotProduct, RunnerError> {
    let ptr_arg_0 = ptr_arg_0.to_usize();
    let ptr_arg_1 = ptr_arg_1.to_usize();
    let ptr_res = ptr_res.to_usize();

    let slice_0 = memory.get_continuous_slice_of_ef_elements(ptr_arg_0, size)?;

    let (slice_1, dot_product_result) = if ptr_arg_1 == ONE_VEC_PTR * VECTOR_LEN {
        if size != 1 {
            unimplemented!("weird use case");
        }
        (vec![EF::ONE], slice_0[0])
    } else {
        let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1, size)?;
        let dot_product_result =
            dot_product::<EF, _, _>(slice_0.iter().copied(), slice_1.iter().copied());
        (slice_1, dot_product_result)
    };

    memory.set_ef_element(ptr_res, dot_product_result)?;

    Ok(WitnessDotProduct {
        addr_0: ptr_arg_0,
        addr_1: ptr_arg_1,
        addr_res: ptr_res,
        len: size,
        slice_0: slice_0.clone(),
        slice_1: slice_1.clone(),
        res: dot_product_result,
    })
}
