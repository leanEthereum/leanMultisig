mod full_round;
pub use full_round::*;

mod partial_round;
pub use partial_round::*;

mod batch_partial_rounds;
pub use batch_partial_rounds::*;

use p3_koala_bear::{
    KOALABEAR_RC16_EXTERNAL_FINAL, KOALABEAR_RC16_EXTERNAL_INITIAL, KOALABEAR_RC16_INTERNAL,
    KOALABEAR_RC24_EXTERNAL_FINAL, KOALABEAR_RC24_EXTERNAL_INITIAL, KOALABEAR_RC24_INTERNAL,
};

use crate::F;

#[derive(Debug)]
pub struct PoseidonGKRLayers<const WIDTH: usize, const N_COMMITED_CUBES: usize> {
    pub initial_full_round: FullRoundComputation<WIDTH, true>,
    pub initial_full_rounds_remaining: Vec<FullRoundComputation<WIDTH, false>>,
    pub batch_partial_rounds: BatchPartialRounds<WIDTH, N_COMMITED_CUBES>,
    pub partial_rounds_remaining: Vec<PartialRoundComputation<WIDTH>>,
    pub final_full_rounds: Vec<FullRoundComputation<WIDTH, false>>,
}

impl<const WIDTH: usize, const N_COMMITED_CUBES: usize> PoseidonGKRLayers<WIDTH, N_COMMITED_CUBES> {
    pub fn build(compressed_output: Option<usize>) -> Self {
        match WIDTH {
            16 => unsafe {
                Self::build_generic(
                    &*(&KOALABEAR_RC16_EXTERNAL_INITIAL as *const [[F; 16]]
                        as *const [[F; WIDTH]]),
                    &KOALABEAR_RC16_INTERNAL,
                    &*(&KOALABEAR_RC16_EXTERNAL_FINAL as *const [[F; 16]] as *const [[F; WIDTH]]),
                    compressed_output,
                )
            },
            24 => unsafe {
                Self::build_generic(
                    &*(&KOALABEAR_RC24_EXTERNAL_INITIAL as *const [[F; 24]]
                        as *const [[F; WIDTH]]),
                    &KOALABEAR_RC24_INTERNAL,
                    &*(&KOALABEAR_RC24_EXTERNAL_FINAL as *const [[F; 24]] as *const [[F; WIDTH]]),
                    compressed_output,
                )
            },
            _ => panic!("Only Poseidon 16 and 24 are supported currently"),
        }
    }

    fn build_generic(
        initial_constants: &[[F; WIDTH]],
        internal_constants: &[F],
        final_constants: &[[F; WIDTH]],
        compressed_output: Option<usize>,
    ) -> Self {
        let initial_full_round = FullRoundComputation {
            constants: initial_constants[0],
            compressed_output: None,
        };
        let initial_full_rounds_remaining = initial_constants[1..]
            .iter()
            .map(|&constants| FullRoundComputation {
                constants,
                compressed_output: None,
            })
            .collect::<Vec<_>>();
        let batch_partial_rounds = BatchPartialRounds {
            constants: internal_constants[..N_COMMITED_CUBES].try_into().unwrap(),
            last_constant: internal_constants[N_COMMITED_CUBES],
        };
        let partial_rounds_remaining = internal_constants[N_COMMITED_CUBES + 1..]
            .iter()
            .map(|&constant| PartialRoundComputation { constant })
            .collect::<Vec<_>>();
        let final_full_rounds = final_constants
            .iter()
            .enumerate()
            .map(|(i, &constants)| FullRoundComputation {
                constants,
                compressed_output: if i == final_constants.len() - 1 {
                    compressed_output
                } else {
                    None
                },
            })
            .collect::<Vec<_>>();
        Self {
            initial_full_round,
            initial_full_rounds_remaining,
            batch_partial_rounds,
            partial_rounds_remaining,
            final_full_rounds,
        }
    }
}
