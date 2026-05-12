use backend::*;

use crate::Poseidon8;
use crate::get_poseidon8;

pub type VarCount = usize;

pub fn build_prover_state() -> ProverState<CubicExtensionFieldGL, Poseidon8> {
    ProverState::new(*get_poseidon8())
}

pub fn build_verifier_state(
    prover_state: ProverState<CubicExtensionFieldGL, Poseidon8>,
) -> Result<VerifierState<CubicExtensionFieldGL, Poseidon8>, ProofError> {
    VerifierState::new(prover_state.into_proof(), *get_poseidon8())
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
