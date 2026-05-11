use tracing::instrument;

use crate::F;
use crate::tables::poseidon_16::{
    POSEIDON_16_COL_COMPRESSED_OUTPUT_START, POSEIDON_16_COL_GKR_START, POSEIDON_16_COL_INPUT_START,
};
use backend::*;
use poseidon_gkr::fill_poseidon_gkr_trace;

/// Fill the GKR-layer columns and the lower half of the compressed-output columns from the input columns.
///
/// The 4 AIR/index columns, the inputs, the *upper* half of compressed_output[4..8], and the
/// 4 eff_second columns are assumed to be already filled by `execute()`. We compute the GKR layer
/// columns from the inputs and overwrite compressed_output[0..4] = perm_state[0..4] + input[0..4].
///
/// Note: although `execute()` already wrote correct compressed_output values (it had the actual
/// poseidon outputs in hand), we recompute the *lower* 4 here too so that this function is
/// self-consistent and so that the compressed_output cols are recomputed from the GKR-layer
/// output (a useful sanity check during witness generation).
#[instrument(name = "generate Poseidon16 trace", skip_all)]
pub fn fill_trace_poseidon_16(trace: &mut [Vec<F>]) {
    // Pad shorter columns up to the trace height.
    let n = trace.iter().map(|col| col.len()).max().unwrap();
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }

    fill_poseidon_gkr_trace(
        trace,
        POSEIDON_16_COL_INPUT_START,
        POSEIDON_16_COL_GKR_START,
        POSEIDON_16_COL_COMPRESSED_OUTPUT_START,
    );
}
