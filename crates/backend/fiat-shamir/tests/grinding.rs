use goldilocks::{CubicExtensionFieldGL, default_goldilocks_poseidon1_8};
use mt_fiat_shamir::{FSProver, FSVerifier, ProverState, VerifierState};
use std::time::Instant;

type EF = CubicExtensionFieldGL;

#[test]
#[ignore]
fn bench_grinding() {
    let n_reps = 100;
    for grinding_bits in 20..=20 {
        let mut prover_state = ProverState::<EF, _>::new(default_goldilocks_poseidon1_8());
        let time = Instant::now();
        for _ in 0..n_reps {
            prover_state.pow_grinding(grinding_bits);
        }
        let elapsed = time.elapsed();
        let mut verifier_state =
            VerifierState::<EF, _>::new(prover_state.into_proof(), default_goldilocks_poseidon1_8()).unwrap();
        for _ in 0..n_reps {
            verifier_state.check_pow_grinding(grinding_bits).unwrap()
        }
        println!("Grinding {grinding_bits} bits: {:?}", elapsed / n_reps);
    }
}
