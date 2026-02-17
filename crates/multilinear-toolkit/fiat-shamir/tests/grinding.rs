use koala_bear::{
    ExternalLayerConstants, KOALABEAR_RC16_EXTERNAL_FINAL, KOALABEAR_RC16_EXTERNAL_INITIAL, KOALABEAR_RC16_INTERNAL,
    Poseidon2KoalaBear, QuinticExtensionFieldKB,
};
use mt_fiat_shamir::{FSProver, FSVerifier, ProverState, VerifierState};
use std::time::Instant;

type EF = QuinticExtensionFieldKB;

#[test]
#[ignore]
fn bench_grinding() {
    let n_reps = 100;
    for grinding_bits in 10..=20 {
        let mut prover_state = ProverState::<EF, _>::new(get_poseidon16());
        let time = Instant::now();
        for _ in 0..n_reps {
            prover_state.pow_grinding(grinding_bits);
        }
        let elapsed = time.elapsed();
        let mut verifier_state = VerifierState::<EF, _>::new(prover_state.raw_proof(), get_poseidon16());
        for _ in 0..n_reps {
            verifier_state.check_pow_grinding(grinding_bits).unwrap()
        }
        println!("Grinding {grinding_bits} bits: {:?}", elapsed / n_reps);
    }
}

pub fn get_poseidon16() -> Poseidon2KoalaBear<16> {
    let external_constants = ExternalLayerConstants::new(
        KOALABEAR_RC16_EXTERNAL_INITIAL.to_vec(),
        KOALABEAR_RC16_EXTERNAL_FINAL.to_vec(),
    );
    Poseidon2KoalaBear::new(external_constants, KOALABEAR_RC16_INTERNAL.to_vec())
}
