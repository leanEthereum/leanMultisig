#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::array;
use utils::{build_prover_state, build_verifier_state, transposed_par_iter_mut};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const UNIVARIATE_SKIPS: usize = 3;

fn main() {
    let mut rng = StdRng::seed_from_u64(0);
    let log_n_poseidons = 11;
    let n_poseidons = 1 << log_n_poseidons;
    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; 16]>>();
    let input_layers: [_; 16] =
        array::from_fn(|i| perm_inputs.par_iter().map(|x| x[i]).collect::<Vec<F>>());

    let partial_round_1 = PartialRoundComputation {
        constant: rng.random(),
        diag: rng.random(),
    };
    let ful_round_1 = FullRoundComputation {
        constants: rng.random(),
        matrix: rng.random(),
    };
    let ful_round_2 = FullRoundComputation {
        constants: rng.random(),
        matrix: rng.random(),
    };

    let output_claim_point = (0..(log_n_poseidons + 1 - UNIVARIATE_SKIPS))
        .map(|_| rng.random())
        .collect::<Vec<EF>>();

    let mut prover_state = build_prover_state::<EF>();

    {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let partial_output_layer_1 = apply_partial_round(&input_layers, &partial_round_1);
        let full_output_layers_1 = apply_full_round(&partial_output_layer_1, &ful_round_1);
        let full_output_layers_2 = apply_full_round(&full_output_layers_1, &ful_round_2);

        let mut output_claims = full_output_layers_2
            .par_iter()
            .map(|output_layer| multilvariate_eval(output_layer, &output_claim_point))
            .collect::<Vec<EF>>();

        prover_state.add_extension_scalars(&output_claims);

        let mut claim_point = output_claim_point.clone();
        for (input_layers, output_layers, full_round) in [
            (&full_output_layers_1, &full_output_layers_2, &ful_round_2),
            (&partial_output_layer_1, &full_output_layers_1, &ful_round_1),
        ] {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                full_round,
                input_layers,
                output_layers,
                &claim_point,
                &output_claims,
            );
        }

        prove_gkr_round(
            &mut prover_state,
            &partial_round_1,
            &input_layers,
            &partial_output_layer_1,
            &claim_point,
            &output_claims,
        );
    }

    {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let mut verifier_state = build_verifier_state(&prover_state);

        let mut output_claims = verifier_state.next_extension_scalars_vec(16).unwrap();

        let mut claim_point = output_claim_point.clone();
        for full_round in [&ful_round_2, &ful_round_1] {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                full_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }

        (claim_point, output_claims) = verify_gkr_round(
            &mut verifier_state,
            &partial_round_1,
            log_n_poseidons,
            &claim_point,
            &output_claims,
        );

        for i in 0..16 {
            assert_eq!(
                output_claims[i],
                multilvariate_eval(&input_layers[i], &claim_point)
            );
        }
    }
}

fn apply_full_round(input_layers: &[Vec<F>], ful_round: &FullRoundComputation) -> [Vec<F>; 16] {
    let mut output_layers: [_; 16] = array::from_fn(|_| F::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let intermediate: [F; 16] =
                array::from_fn(|j| (input_layers[j][row_index] + ful_round.constants[j]).cube());
            output_row.into_iter().enumerate().for_each(|(j, output)| {
                let mut res = F::ZERO;
                for k in 0..16 {
                    res += ful_round.matrix[j][k] * intermediate[k];
                }
                *output = res;
            });
        });
    output_layers
}

fn apply_partial_round(
    input_layers: &[Vec<F>],
    partial_round: &PartialRoundComputation,
) -> [Vec<F>; 16] {
    let mut output_layers: [_; 16] = array::from_fn(|_| F::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .enumerate()
        .for_each(|(row_index, output_row)| {
            let first_cubed = (input_layers[0][row_index] + partial_round.constant).cube();
            let sum: F = first_cubed
                + input_layers
                    .iter()
                    .skip(1)
                    .map(|layer| layer[row_index])
                    .sum::<F>();
            *output_row[0] = sum + first_cubed * partial_round.diag[0];
            for j in 1..16 {
                *output_row[j] = sum + input_layers[j][row_index] * partial_round.diag[j];
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
    input_layers: &[Vec<F>],
    output_layers: &[Vec<F>],
    claim_point: &[EF],
    output_claims: &[EF],
) -> (Vec<EF>, Vec<EF>) {
    let batching_scalar = prover_state.sample();
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());
    let batching_scalars_powers = batching_scalar.powers().collect_n(16);
    let batched_output_layer = batch_layer(output_layers, &batching_scalars_powers);

    debug_assert_eq!(
        batched_claim,
        multilvariate_eval(&batched_output_layer, &claim_point)
    );

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        UNIVARIATE_SKIPS,
        MleGroupRef::Base(input_layers.iter().map(Vec::as_slice).collect()),
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

fn batch_layer(layers: &[Vec<F>], batching_scalars_powers: &[EF]) -> Vec<EF> {
    let n_layers = layers.len();
    let height = layers[0].len();
    (0..height)
        .into_par_iter()
        .map(|i| {
            dot_product(
                batching_scalars_powers.iter().copied(),
                (0..n_layers).map(|j| layers[j][i]),
            )
        })
        .collect::<Vec<EF>>()
}

pub struct FullRoundComputation {
    pub constants: [F; 16],
    pub matrix: [[F; 16]; 16],
}

impl<NF: ExtensionField<F>, EF: ExtensionField<NF>> SumcheckComputation<NF, EF>
    for FullRoundComputation
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        debug_assert_eq!(point.len(), 16);
        let intermediate: [NF; 16] = array::from_fn(|j| (point[j] + self.constants[j]).cube());
        let mut res = EF::ZERO;
        for j in 0..16 {
            let mut temp = NF::ZERO;
            for k in 0..16 {
                temp += intermediate[k] * self.matrix[j][k];
            }
            res += alpha_powers[j] * temp;
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
        let intermediate: [PFPacking<EF>; 16] =
            array::from_fn(|j| (point[j] + self.constants[j]).cube());
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            let mut temp = PFPacking::<EF>::ZERO;
            for k in 0..16 {
                temp += intermediate[k] * self.matrix[j][k];
            }
            res += alpha_powers[j] * temp;
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let intermediate: [EFPacking<EF>; 16] =
            array::from_fn(|j| (point[j] + self.constants[j]).cube());
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            let mut temp = EFPacking::<EF>::ZERO;
            for k in 0..16 {
                temp += intermediate[k] * self.matrix[j][k];
            }
            res += temp * alpha_powers[j];
        }
        res
    }
}

pub struct PartialRoundComputation {
    pub constant: F,
    pub diag: [F; 16],
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
        let sum = first_cubed + point[1..].iter().copied().sum::<NF>();
        let mut res = alpha_powers[0] * (sum + first_cubed * self.diag[0]);
        for j in 1..16 {
            res += alpha_powers[j] * (sum + point[j] * self.diag[j]);
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
        let sum = first_cubed + point[1..].iter().copied().sum::<PFPacking<EF>>();
        let mut res = EFPacking::<EF>::from(alpha_powers[0]) * (sum + first_cubed * self.diag[0]);
        for j in 1..16 {
            res += EFPacking::<EF>::from(alpha_powers[j]) * (sum + point[j] * self.diag[j]);
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let first_cubed = (point[0] + self.constant).cube();
        let sum = first_cubed + point[1..].iter().copied().sum::<EFPacking<EF>>();
        let mut res = EFPacking::<EF>::from(alpha_powers[0]) * (sum + first_cubed * self.diag[0]);
        for j in 1..16 {
            res += EFPacking::<EF>::from(alpha_powers[j]) * (sum + point[j] * self.diag[j]);
        }
        res
    }
}
