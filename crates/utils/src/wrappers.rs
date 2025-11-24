use multilinear_toolkit::prelude::*;
use p3_challenger::DuplexChallenger;
use p3_koala_bear::KoalaBear;

use crate::Poseidon16;
use crate::get_poseidon16;

pub type FSProver<EF, Challenger> = ProverState<PF<EF>, EF, Challenger>;
pub type FSVerifier<EF, Challenger> = VerifierState<PF<EF>, EF, Challenger>;

pub type MyChallenger = DuplexChallenger<KoalaBear, Poseidon16, 16, 8>;

pub fn build_challenger() -> MyChallenger {
    MyChallenger::new(get_poseidon16().clone())
}

pub fn build_prover_state<EF: ExtensionField<KoalaBear>>() -> ProverState<KoalaBear, EF, MyChallenger> {
    ProverState::new(build_challenger())
}

pub fn build_verifier_state<EF: ExtensionField<KoalaBear>>(
    prover_state: ProverState<KoalaBear, EF, MyChallenger>,
) -> VerifierState<KoalaBear, EF, MyChallenger> {
    VerifierState::new(prover_state.into_proof(), build_challenger())
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
