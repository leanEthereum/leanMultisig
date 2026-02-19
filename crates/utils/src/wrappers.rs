use backend::*;

use crate::Poseidon16;
use crate::get_poseidon16;

pub type VarCount = usize;

pub fn build_prover_state() -> ProverState<QuinticExtensionFieldKB, Poseidon16> {
    ProverState::new(get_poseidon16().clone())
}

pub fn build_verifier_state(
    prover_state: ProverState<QuinticExtensionFieldKB, Poseidon16>,
) -> VerifierState<QuinticExtensionFieldKB, Poseidon16> {
    VerifierState::new(prover_state.raw_proof(), get_poseidon16().clone())
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
