#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC16_EXTERNAL_FINAL,
    KOALABEAR_RC16_EXTERNAL_INITIAL, KOALABEAR_RC16_INTERNAL, KoalaBear, QuinticExtensionFieldKB,
};
use p3_poseidon2::GenericPoseidon2LinearLayers;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{array, time::Instant};
use tracing::instrument;
use utils::{
    build_prover_state, build_verifier_state, init_tracing, poseidon16_permute,
    transposed_par_iter_mut,
};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const UNIVARIATE_SKIPS: usize = 3;

const SANITY_CHECK: bool = false;

fn main() {
    init_tracing();

    let mut rng = StdRng::seed_from_u64(0);
    let log_n_poseidons = 19;
    let n_poseidons = 1 << log_n_poseidons;
    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; 16]>>();
    let input_layers: [_; 16] =
        array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());

    let initial_full_rounds = KOALABEAR_RC16_EXTERNAL_INITIAL
        .into_iter()
        .enumerate()
        .map(|(i, constants)| FullRoundComputation {
            constants,
            first_full_round: i == 0,
        })
        .collect::<Vec<_>>();
    let mid_partial_rounds = KOALABEAR_RC16_INTERNAL
        .into_iter()
        .map(|constant| PartialRoundComputation { constant })
        .collect::<Vec<_>>();
    let final_full_rounds = KOALABEAR_RC16_EXTERNAL_FINAL
        .into_iter()
        .map(|constants| FullRoundComputation {
            constants,
            first_full_round: false,
        })
        .collect::<Vec<_>>();

    let n_initial_full_rounds = initial_full_rounds.len();
    let n_mid_partial_rounds = mid_partial_rounds.len();
    let n_final_full_rounds = final_full_rounds.len();

    let output_claim_point = (0..(log_n_poseidons + 1 - UNIVARIATE_SKIPS))
        .map(|_| rng.random())
        .collect::<Vec<EF>>();

    let mut prover_state = build_prover_state::<EF>();

    let prover_time = Instant::now();
    {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let input_layers_packed: [_; 16] =
            array::from_fn(|i| PFPacking::<EF>::pack_slice(&input_layers[i]).to_vec());
        let mut all_layers = vec![input_layers_packed];
        for (i, round) in initial_full_rounds.iter().enumerate() {
            all_layers.push(apply_full_round(all_layers.last().unwrap(), round, i == 0));
        }
        for round in &mid_partial_rounds {
            all_layers.push(apply_partial_round(all_layers.last().unwrap(), round));
        }
        for round in &final_full_rounds {
            all_layers.push(apply_full_round(all_layers.last().unwrap(), round, false));
        }
        let initial_full_layers = &all_layers[..n_initial_full_rounds];
        let mid_partial_layers =
            &all_layers[n_initial_full_rounds..n_initial_full_rounds + n_mid_partial_rounds];
        let final_full_layers = &all_layers[n_initial_full_rounds + n_mid_partial_rounds
            ..n_initial_full_rounds + n_mid_partial_rounds + n_final_full_rounds];

        if SANITY_CHECK {
            let perm_outputs = perm_inputs
                .par_iter()
                .map(|input| poseidon16_permute(*input))
                .collect::<Vec<_>>();
            let last_layers: [_; 16] =
                array::from_fn(|i| PFPacking::<EF>::unpack_slice(&all_layers.last().unwrap()[i]));
            (0..n_poseidons).into_par_iter().for_each(|row| {
                for i in 0..16 {
                    assert_eq!(perm_outputs[row][i], last_layers[i][row]);
                }
            });
        }

        let mut output_claims = all_layers
            .last()
            .unwrap()
            .par_iter()
            .map(|output_layer| {
                multilvariate_eval(
                    PFPacking::<EF>::unpack_slice(&output_layer),
                    &output_claim_point,
                )
            })
            .collect::<Vec<EF>>();

        prover_state.add_extension_scalars(&output_claims);

        let mut claim_point = output_claim_point.clone();
        for (input_layers, full_round) in final_full_layers.iter().zip(&final_full_rounds).rev() {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                full_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        for (input_layers, partial_round) in
            mid_partial_layers.iter().zip(&mid_partial_rounds).rev()
        {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                partial_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        for (input_layers, full_round) in initial_full_layers.iter().zip(&initial_full_rounds).rev()
        {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                full_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }
    }
    let prover_duration = prover_time.elapsed();

    let verifier_time = Instant::now();
    {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let mut verifier_state = build_verifier_state(&prover_state);

        let mut output_claims = verifier_state.next_extension_scalars_vec(16).unwrap();

        let mut claim_point = output_claim_point.clone();
        for full_round in final_full_rounds.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                full_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }

        for partial_round in mid_partial_rounds.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                partial_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }

        for full_round in initial_full_rounds.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                full_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }

        for i in 0..16 {
            assert_eq!(
                output_claims[i],
                multilvariate_eval(&input_layers[i], &claim_point)
            );
        }
    }
    let verifier_duration = verifier_time.elapsed();

    println!("GKR proof for {} Poseidon2:", n_poseidons);
    println!(
        "Prover time: {:?} ({:.1} Poseidons / s)",
        prover_duration,
        n_poseidons as f64 / prover_duration.as_secs_f64()
    );
    println!("Verifier time: {:?}", verifier_duration);
}

#[instrument(skip_all)]
fn apply_full_round(
    input_layers: &[Vec<PFPacking<EF>>],
    ful_round: &FullRoundComputation,
    first_full_round: bool,
) -> [Vec<PFPacking<EF>>; 16] {
    let mut output_layers: [_; 16] =
        array::from_fn(|_| PFPacking::<EF>::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let mut intermediate: [PFPacking<EF>; 16] =
                array::from_fn(|j| input_layers[j][row_index]);
            if first_full_round {
                GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
            }
            intermediate
                .par_iter_mut()
                .enumerate()
                .for_each(|(j, val)| {
                    *val = (*val + ful_round.constants[j]).cube();
                });
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
            for j in 0..16 {
                *output_row[j] = intermediate[j];
            }
        });
    output_layers
}

#[instrument(skip_all)]
fn apply_partial_round(
    input_layers: &[Vec<PFPacking<EF>>],
    partial_round: &PartialRoundComputation,
) -> [Vec<PFPacking<EF>>; 16] {
    let mut output_layers: [_; 16] =
        array::from_fn(|_| PFPacking::<EF>::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let first_cubed = (input_layers[0][row_index] + partial_round.constant).cube();
            let mut intermediate = [PFPacking::<EF>::ZERO; 16];
            intermediate[0] = first_cubed;
            for j in 1..16 {
                intermediate[j] = input_layers[j][row_index];
            }
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut intermediate);
            for j in 0..16 {
                *output_row[j] = intermediate[j];
            }
        });
    output_layers
}

fn prove_gkr_round<
    SC: SumcheckComputation<F, EF>
        + SumcheckComputation<EF, EF>
        + SumcheckComputationPacked<EF>
        + 'static,
>(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    computation: &SC,
    input_layers: &[Vec<PFPacking<EF>>],
    claim_point: &[EF],
    output_claims: &[EF],
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = prover_state.sample();
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());
    let batching_scalars_powers = batching_scalar.powers().collect_n(16);

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        UNIVARIATE_SKIPS,
        MleGroupRef::BasePacked(input_layers.iter().map(Vec::as_slice).collect()),
        computation,
        computation,
        &batching_scalars_powers,
        Some((claim_point.to_vec(), None)),
        false,
        prover_state,
        batched_claim,
        None,
    );

    // sanity check
    debug_assert_eq!(
        computation.eval(&sumcheck_inner_evals, &batching_scalars_powers)
            * eq_poly_with_skip(&sumcheck_point, &claim_point, UNIVARIATE_SKIPS),
        sumcheck_final_sum
    );

    prover_state.add_extension_scalars(&sumcheck_inner_evals);

    (sumcheck_point.0, sumcheck_inner_evals)
}

fn verify_gkr_round<SC: SumcheckComputation<EF, EF>>(
    verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
    computation: &SC,
    log_n_poseidons: usize,
    claim_point: &[EF],
    output_claims: &[EF],
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = verifier_state.sample();
    let batching_scalars_powers = batching_scalar.powers().collect_n(16);
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());

    let (retrieved_batched_claim, sumcheck_postponed_claim) =
        sumcheck_verify_with_univariate_skip(verifier_state, 4, log_n_poseidons, UNIVARIATE_SKIPS)
            .unwrap();

    assert_eq!(retrieved_batched_claim, batched_claim);

    let sumcheck_inner_evals = verifier_state.next_extension_scalars_vec(16).unwrap();
    assert_eq!(
        computation.eval(&sumcheck_inner_evals, &batching_scalars_powers)
            * eq_poly_with_skip(
                &sumcheck_postponed_claim.point,
                &claim_point,
                UNIVARIATE_SKIPS
            ),
        sumcheck_postponed_claim.value
    );

    (sumcheck_postponed_claim.point.0, sumcheck_inner_evals)
}

fn multilvariate_eval<F: Field, EF: ExtensionField<F>>(poly: &[F], point: &[EF]) -> EF {
    assert_eq!(poly.len(), 1 << (point.len() + UNIVARIATE_SKIPS - 1));
    univariate_selectors::<F>(UNIVARIATE_SKIPS)
        .iter()
        .zip(poly.chunks_exact(1 << (point.len() - 1)))
        .map(|(selector, chunk)| {
            selector.evaluate(point[0]) * chunk.evaluate(&MultilinearPoint(point[1..].to_vec()))
        })
        .sum()
}

pub struct FullRoundComputation {
    pub constants: [F; 16],
    pub first_full_round: bool,
}

impl<NF: ExtensionField<F>, EF: ExtensionField<NF>> SumcheckComputation<NF, EF>
    for FullRoundComputation
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), 16);
        let mut intermediate: [NF; 16] = array::from_fn(|j| point[j]);
        if self.first_full_round {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
        }
        intermediate.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + self.constants[j]).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
        let mut res = EF::ZERO;
        for i in 0..16 {
            res += alpha_powers[i] * intermediate[i];
        }
        res
    }
}

impl SumcheckComputationPacked<EF> for FullRoundComputation {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let mut intermediate: [PFPacking<EF>; 16] = array::from_fn(|j| point[j]);
        if self.first_full_round {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
        }
        intermediate.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + self.constants[j]).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += EFPacking::<EF>::from(alpha_powers[j]) * intermediate[j];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let mut intermediate: [EFPacking<EF>; 16] = array::from_fn(|j| point[j]);
        if self.first_full_round {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
        }
        intermediate.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + PFPacking::<EF>::from(self.constants[j])).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut intermediate);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += intermediate[j] * alpha_powers[j];
        }
        res
    }
}

pub struct PartialRoundComputation {
    pub constant: F,
}

impl<NF: ExtensionField<F>, EF: ExtensionField<NF>> SumcheckComputation<NF, EF>
    for PartialRoundComputation
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), 16);
        let first_cubed = (point[0] + self.constant).cube();
        let mut intermediate = [NF::ZERO; 16];
        intermediate[0] = first_cubed;
        for j in 1..16 {
            intermediate[j] = point[j];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut intermediate);
        let mut res = EF::ZERO;
        for i in 0..16 {
            res += alpha_powers[i] * intermediate[i];
        }
        res
    }
}

impl SumcheckComputationPacked<EF> for PartialRoundComputation {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let first_cubed = (point[0] + self.constant).cube();
        let mut intermediate = [PFPacking::<EF>::ZERO; 16];
        intermediate[0] = first_cubed;
        for j in 1..16 {
            intermediate[j] = point[j];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut intermediate);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += EFPacking::<EF>::from(alpha_powers[j]) * intermediate[j];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let first_cubed = (point[0] + PFPacking::<EF>::from(self.constant)).cube();
        let mut intermediate = [EFPacking::<EF>::ZERO; 16];
        intermediate[0] = first_cubed;
        for j in 1..16 {
            intermediate[j] = point[j];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut intermediate);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += intermediate[j] * alpha_powers[j];
        }
        res
    }
}
