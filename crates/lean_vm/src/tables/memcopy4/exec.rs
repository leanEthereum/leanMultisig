use crate::tables::memcopy4::{MEMCOPY4_DOMAIN_SEP, MEMCOPY4_LEN_MULT, MEMCOPY4_STRIDE_OUT, MEMCOPY4_STRIDES, air::*};
use crate::{F, MemoryAccess, RunnerError, TableTrace};
use backend::*;
use utils::ToUsize;

/// Execute a memcopy4 call: copy 4 field elements `n_reps` times from `ptr_in`
/// to `ptr_out`, advancing source by `MEMCOPY4_STRIDES[variant]` and destination
/// by `MEMCOPY4_STRIDE_OUT` per iteration.
///
/// `stride_in_flag`: 1 → stride = MEMCOPY4_STRIDES[0], 0 → stride = MEMCOPY4_STRIDES[1].
pub(super) fn exec_memcopy4(
    ptr_in: F,
    ptr_out: F,
    stride_in_flag: usize,
    n_reps: usize,
    memory: &mut impl MemoryAccess,
    trace: &mut TableTrace,
) -> Result<(), RunnerError> {
    assert!(n_reps >= 1);
    assert!(stride_in_flag <= 1);
    let stride_in = if stride_in_flag == 1 {
        MEMCOPY4_STRIDES[0]
    } else {
        MEMCOPY4_STRIDES[1]
    };
    let stride_in_flag_f = F::from_usize(stride_in_flag);
    let aux_base = MEMCOPY4_DOMAIN_SEP + stride_in_flag;

    for i in 0..n_reps {
        let src_addr = ptr_in.to_usize() + i * stride_in;
        let dst_addr = ptr_out.to_usize() + i * MEMCOPY4_STRIDE_OUT;

        for k in 0..4 {
            let v = memory.get(src_addr + k)?;
            memory.set(dst_addr + k, v)?;
        }

        let is_start = i == 0;
        let current_len = n_reps - i;

        trace.columns[COL_MC4_ACTIVATION].push(F::from_bool(is_start));
        trace.columns[COL_START].push(F::from_bool(is_start));
        trace.columns[COL_STRIDE_IN_FLAG].push(stride_in_flag_f);
        trace.columns[COL_LEN].push(F::from_usize(current_len));
        trace.columns[COL_ADDR_IN].push(F::from_usize(src_addr));
        trace.columns[COL_ADDR_OUT].push(F::from_usize(dst_addr));

        // Data columns: filled post-execute by fill_trace_memcopy4.
        for k in 0..4 {
            trace.columns[COL_DATA + k].push(F::ZERO);
        }

        // Virtual column.
        trace.columns[COL_MC4_AUX].push(F::from_usize(aux_base + MEMCOPY4_LEN_MULT * current_len));
    }

    Ok(())
}

/// Post-execute: fill the 4 data columns from the final memory state.
pub fn fill_trace_memcopy4(trace: &mut TableTrace, memory: &[F]) {
    let n = trace.columns[COL_ADDR_IN].len();
    for i in 0..n {
        let addr = trace.columns[COL_ADDR_IN][i].to_usize();
        for k in 0..4 {
            trace.columns[COL_DATA + k][i] = memory[addr + k];
        }
    }
}
