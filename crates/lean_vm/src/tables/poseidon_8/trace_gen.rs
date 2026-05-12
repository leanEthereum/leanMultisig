use tracing::instrument;

use crate::F;
use backend::PrimeCharacteristicRing;

// `execute()` writes every column for each active row (I/O + all per-round
// witness cols), and `padding_row()` supplies the zero-input witness for
// trailing padding. This pass just equalises column lengths in case any got
// out of sync during trace construction.
#[instrument(name = "generate Poseidon8 AIR trace", skip_all)]
pub fn fill_trace_poseidon_8(trace: &mut [Vec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap_or(0);
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }
}
