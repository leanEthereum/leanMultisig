use multilinear_toolkit::prelude::*;
use p3_koala_bear::QuinticExtensionFieldKB;

use crate::Poseidon16;
use crate::get_poseidon16;

pub fn build_prover_state() -> ProverState<QuinticExtensionFieldKB, Poseidon16> {
    let mut prover_state = ProverState::new(get_poseidon16().clone());
    prover_state.duplexing();
    prover_state
}

pub fn build_verifier_state(
    prover_state: ProverState<QuinticExtensionFieldKB, Poseidon16>,
) -> VerifierState<QuinticExtensionFieldKB, Poseidon16> {
    let mut verifier_state = VerifierState::new(prover_state.into_proof(), get_poseidon16().clone());
    verifier_state.duplexing();
    verifier_state
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
