use tracing::instrument;

use crate::F;
use backend::PrimeCharacteristicRing;

// TODO(goldilocks-migration): once the Goldilocks Poseidon1-8 AIR has real
// per-round witness columns, this is where we'll fill them. Today the stub AIR
// has no per-round columns, so the `execute` path already writes every column
// it needs.
#[instrument(name = "generate Poseidon8 AIR trace (stub)", skip_all)]
pub fn fill_trace_poseidon_8(trace: &mut [Vec<F>]) {
    let n = trace.iter().map(|col| col.len()).max().unwrap_or(0);
    for col in trace.iter_mut() {
        if col.len() != n {
            col.resize(n, F::ZERO);
        }
    }
}
