#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC16_EXTERNAL_FINAL,
    KOALABEAR_RC16_EXTERNAL_INITIAL, KOALABEAR_RC16_INTERNAL, KoalaBear, QuinticExtensionFieldKB,
};
use p3_poseidon2::GenericPoseidon2LinearLayers;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{array, time::Instant};
use tracing::{info_span, instrument};
use utils::{
    build_prover_state, build_verifier_state, init_tracing, poseidon16_permute,
    transposed_par_iter_mut,
};
use whir_p3::{FoldingFactor, SecurityAssumption, WhirConfig, WhirConfigBuilder};

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;
const UNIVARIATE_SKIPS: usize = 3;

const SANITY_CHECK: bool = false;
const N_COMMITED_CUBES: usize = 16; // power of 2 to increase PCS efficiency

// const N_INITIAL_ROUNDS: usize = KOALABEAR_RC16_EXTERNAL_INITIAL.len();
const N_INTERNAL_ROUNDS: usize = KOALABEAR_RC16_INTERNAL.len();
// const N_FINAL_ROUNDS: usize = KOALABEAR_RC16_EXTERNAL_FINAL.len();

fn main() {
    assert!(N_COMMITED_CUBES <= N_INTERNAL_ROUNDS);
    init_tracing();

    let log_n_poseidons = 20;

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
    };
    let whir_n_vars = log_n_poseidons + log2_strict_usize(16 + N_COMMITED_CUBES);
    let whir_config = WhirConfig::new(whir_config_builder, whir_n_vars);

    let mut rng = StdRng::seed_from_u64(0);
    let n_poseidons = 1 << log_n_poseidons;
    let perm_inputs = (0..n_poseidons)
        .map(|_| rng.random())
        .collect::<Vec<[F; 16]>>();
    let selectors = univariate_selectors::<F>(UNIVARIATE_SKIPS);
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
    let partial_rounds_with_committed_cubes = PartialRoundsWithCommittedCubes {
        constants: KOALABEAR_RC16_INTERNAL[..N_COMMITED_CUBES]
            .try_into()
            .unwrap(),
        last_constant: KOALABEAR_RC16_INTERNAL[N_COMMITED_CUBES],
    };
    let partial_rounds_remaining = KOALABEAR_RC16_INTERNAL[N_COMMITED_CUBES + 1..]
        .iter()
        .copied()
        .map(|constant| PartialRoundComputation { constant })
        .collect::<Vec<_>>();
    let final_full_rounds = KOALABEAR_RC16_EXTERNAL_FINAL
        .into_iter()
        .map(|constants| FullRoundComputation {
            constants,
            first_full_round: false,
        })
        .collect::<Vec<_>>();

    let prover_time = Instant::now();

    let mut verifier_state = {
        // ---------------------------------------------------- PROVER ----------------------------------------------------

        let initial_full_layer_inputs: [_; 16] =
            array::from_fn(|i| PFPacking::<EF>::pack_slice(&input_layers[i]).to_vec());
        let mut all_initial_full_layers = vec![initial_full_layer_inputs];
        for (i, round) in initial_full_rounds.iter().enumerate() {
            all_initial_full_layers.push(apply_full_round(
                all_initial_full_layers.last().unwrap(),
                round,
                i == 0,
            ));
        }

        let internal_partial_layer_with_committed_cubes_inputs =
            all_initial_full_layers.pop().unwrap();
        let (next_layer, committed_cubes) = apply_partial_round_for_commit_cubes(
            &internal_partial_layer_with_committed_cubes_inputs,
            &partial_rounds_with_committed_cubes,
        );

        let mut internal_partial_layer_remaining_inputs = vec![next_layer];
        for round in &partial_rounds_remaining {
            internal_partial_layer_remaining_inputs.push(apply_partial_round(
                internal_partial_layer_remaining_inputs.last().unwrap(),
                round,
            ));
        }

        let mut all_final_full_layers =
            vec![internal_partial_layer_remaining_inputs.pop().unwrap()];
        for round in &final_full_rounds {
            all_final_full_layers.push(apply_full_round(
                all_final_full_layers.last().unwrap(),
                round,
                false,
            ));
        }

        let mut prover_state = build_prover_state::<EF>();
        let mut global_poly_commited: Vec<F> = unsafe { uninitialized_vec(1 << whir_n_vars) };
        let mut chunks = split_at_mut_many(
            &mut global_poly_commited,
            (0..16 + N_COMMITED_CUBES - 1)
                .map(|i| (i + 1) << log_n_poseidons)
                .collect::<Vec<_>>()
                .as_slice(),
        );
        chunks[..16]
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, chunk)| {
                chunk.copy_from_slice(&input_layers[i]);
            });
        chunks[16..]
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, chunk)| {
                chunk.copy_from_slice(PFPacking::<EF>::unpack_slice(&committed_cubes[i]));
            });

        let global_poly_commited = MleOwned::Base(global_poly_commited);
        let pcs_witness = whir_config.commit(&mut prover_state, &global_poly_commited);
        let global_poly_commited_packed =
            PFPacking::<EF>::pack_slice(global_poly_commited.as_base().unwrap());

        if SANITY_CHECK {
            let perm_outputs = perm_inputs
                .par_iter()
                .map(|input| poseidon16_permute(*input))
                .collect::<Vec<_>>();
            let last_layers: [_; 16] = array::from_fn(|i| {
                PFPacking::<EF>::unpack_slice(&all_final_full_layers.last().unwrap()[i])
            });
            (0..n_poseidons).into_par_iter().for_each(|row| {
                for i in 0..16 {
                    assert_eq!(perm_outputs[row][i], last_layers[i][row]);
                }
            });
        }

        let output_claim_point = prover_state.sample_vec(log_n_poseidons + 1 - UNIVARIATE_SKIPS);

        let mut output_claims = info_span!("computing output claims").in_scope(|| {
            all_final_full_layers
                .last()
                .unwrap()
                .par_iter()
                .map(|output_layer| {
                    multivariate_eval::<_, _, _, false>(
                        PFPacking::<EF>::unpack_slice(&output_layer),
                        &output_claim_point,
                        &selectors,
                    )
                })
                .collect::<Vec<EF>>()
        });

        prover_state.add_extension_scalars(&output_claims);

        let mut claim_point = output_claim_point.clone();

        for (input_layers, full_round) in all_final_full_layers.iter().zip(&final_full_rounds).rev()
        {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                full_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        for (input_layers, partial_round) in internal_partial_layer_remaining_inputs
            .iter()
            .zip(&partial_rounds_remaining)
            .rev()
        {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                partial_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        (claim_point, output_claims) = prove_internal_rounds_with_committed_cube(
            &mut prover_state,
            &internal_partial_layer_with_committed_cubes_inputs,
            &committed_cubes,
            &partial_rounds_with_committed_cubes,
            &claim_point,
            &output_claims,
            &selectors,
        );

        let pcs_point_for_cubes = claim_point.clone();
        let pcs_evals_for_cubes = output_claims[16..].to_vec();

        output_claims = output_claims[..16].to_vec();

        for (input_layers, full_round) in all_initial_full_layers
            .iter()
            .zip(&initial_full_rounds)
            .rev()
        {
            (claim_point, output_claims) = prove_gkr_round(
                &mut prover_state,
                full_round,
                input_layers,
                &claim_point,
                &output_claims,
            );
        }

        let pcs_point_for_inputs = claim_point.clone();
        let pcs_evals_for_inputs = output_claims.to_vec();

        // PCS opening
        let mut pcs_statements = vec![];

        let eq_mle_inputs = eval_eq_packed(&pcs_point_for_inputs[1..]);
        let inner_evals_inputs = global_poly_commited_packed
            [..global_poly_commited_packed.len() / 2]
            .par_chunks_exact(eq_mle_inputs.len())
            .map(|chunk| {
                let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                    eq_mle_inputs.iter().copied(),
                    chunk.iter().copied(),
                );
                <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum]).sum::<EF>()
            })
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&inner_evals_inputs);
        let pcs_batching_scalars_inputs = prover_state.sample_vec(4 + UNIVARIATE_SKIPS); // 4 = log2(16)
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ZERO],
                    pcs_batching_scalars_inputs.clone(),
                    pcs_point_for_inputs[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_inputs.evaluate(&MultilinearPoint(pcs_batching_scalars_inputs)),
        });
        {
            // sanity check
            for (&eval, inner_evals) in pcs_evals_for_inputs
                .iter()
                .zip(inner_evals_inputs.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    multivariate_eval::<_, _, _, false>(
                        inner_evals,
                        &pcs_point_for_inputs[..1],
                        &selectors
                    )
                );
            }
        }

        let eq_mle_cubes = eval_eq_packed(&pcs_point_for_cubes[1..]);
        let inner_evals_cubes = global_poly_commited_packed
            [global_poly_commited_packed.len() / 2..]
            .par_chunks_exact(eq_mle_cubes.len())
            .map(|chunk| {
                let ef_sum = dot_product::<EFPacking<EF>, _, _>(
                    eq_mle_cubes.iter().copied(),
                    chunk.iter().copied(),
                );
                <EFPacking<EF> as PackedFieldExtension<F, EF>>::to_ext_iter([ef_sum]).sum::<EF>()
            })
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&inner_evals_cubes);
        let pcs_batching_scalars_cubes =
            prover_state.sample_vec(log2_strict_usize(N_COMMITED_CUBES) + UNIVARIATE_SKIPS);
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ONE],
                    pcs_batching_scalars_cubes.clone(),
                    pcs_point_for_cubes[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_cubes.evaluate(&MultilinearPoint(pcs_batching_scalars_cubes)),
        });
        {
            // sanity check
            for (&eval, inner_evals) in pcs_evals_for_cubes
                .iter()
                .zip(inner_evals_cubes.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    multivariate_eval::<_, _, _, false>(
                        inner_evals,
                        &pcs_point_for_cubes[..1],
                        &selectors
                    )
                );
            }
        }

        whir_config.prove(
            &mut prover_state,
            pcs_statements,
            pcs_witness,
            &global_poly_commited.by_ref(),
        );

        build_verifier_state(&prover_state)
    };

    let prover_duration = prover_time.elapsed();

    let verifier_time = Instant::now();
    {
        // ---------------------------------------------------- VERIFIER ----------------------------------------------------

        let parsed_pcs_commitment = whir_config
            .parse_commitment::<F>(&mut verifier_state)
            .unwrap();

        let output_claim_point = verifier_state.sample_vec(log_n_poseidons + 1 - UNIVARIATE_SKIPS);

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

        for partial_round in partial_rounds_remaining.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                partial_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }
        let claimed_cubes_evals = verifier_state
            .next_extension_scalars_vec(N_COMMITED_CUBES)
            .unwrap();

        (claim_point, output_claims) = verify_gkr_round(
            &mut verifier_state,
            &partial_rounds_with_committed_cubes,
            log_n_poseidons,
            &claim_point,
            &[output_claims, claimed_cubes_evals.clone()].concat(),
        );

        let pcs_point_for_cubes = claim_point.clone();
        let pcs_evals_for_cubes = output_claims[16..].to_vec();

        output_claims = output_claims[..16].to_vec();

        for full_round in initial_full_rounds.iter().rev() {
            (claim_point, output_claims) = verify_gkr_round(
                &mut verifier_state,
                full_round,
                log_n_poseidons,
                &claim_point,
                &output_claims,
            );
        }

        let pcs_point_for_inputs = claim_point.clone();
        let pcs_evals_for_inputs = output_claims.to_vec();

        // PCS verification

        let mut pcs_statements = vec![];

        let inner_evals_inputs = verifier_state
            .next_extension_scalars_vec(16 << UNIVARIATE_SKIPS)
            .unwrap();
        let pcs_batching_scalars_inputs = verifier_state.sample_vec(4 + UNIVARIATE_SKIPS); // 4 = log2(16)
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ZERO],
                    pcs_batching_scalars_inputs.clone(),
                    pcs_point_for_inputs[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_inputs.evaluate(&MultilinearPoint(pcs_batching_scalars_inputs)),
        });
        {
            for (&eval, inner_evals) in pcs_evals_for_inputs
                .iter()
                .zip(inner_evals_inputs.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    multivariate_eval::<_, _, _, false>(
                        inner_evals,
                        &pcs_point_for_inputs[..1],
                        &selectors
                    )
                );
            }
        }

        let inner_evals_cubes = verifier_state
            .next_extension_scalars_vec(N_COMMITED_CUBES << UNIVARIATE_SKIPS)
            .unwrap();
        let pcs_batching_scalars_cubes =
            verifier_state.sample_vec(log2_strict_usize(N_COMMITED_CUBES) + UNIVARIATE_SKIPS);
        pcs_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    vec![EF::ONE],
                    pcs_batching_scalars_cubes.clone(),
                    pcs_point_for_cubes[1..].to_vec(),
                ]
                .concat(),
            ),
            value: inner_evals_cubes.evaluate(&MultilinearPoint(pcs_batching_scalars_cubes)),
        });
        {
            // sanity check
            for (&eval, inner_evals) in pcs_evals_for_cubes
                .iter()
                .zip(inner_evals_cubes.chunks_exact(1 << UNIVARIATE_SKIPS))
            {
                assert_eq!(
                    eval,
                    multivariate_eval::<_, _, _, false>(
                        inner_evals,
                        &pcs_point_for_cubes[..1],
                        &selectors
                    )
                );
            }
        }

        whir_config
            .verify(&mut verifier_state, &parsed_pcs_commitment, pcs_statements)
            .unwrap();
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
            let mut buff: [PFPacking<EF>; 16] = array::from_fn(|j| input_layers[j][row_index]);
            if first_full_round {
                GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
            }
            buff.iter_mut().enumerate().for_each(|(j, val)| {
                *val = (*val + ful_round.constants[j]).cube();
            });
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
            for j in 0..16 {
                *output_row[j] = buff[j];
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
            let mut buff = [PFPacking::<EF>::ZERO; 16];
            buff[0] = first_cubed;
            for j in 1..16 {
                buff[j] = input_layers[j][row_index];
            }
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            for j in 0..16 {
                *output_row[j] = buff[j];
            }
        });
    output_layers
}

#[instrument(skip_all)]
fn apply_partial_round_for_commit_cubes(
    input_layers: &[Vec<PFPacking<EF>>],
    rounds: &PartialRoundsWithCommittedCubes,
) -> (
    [Vec<PFPacking<EF>>; 16],
    [Vec<PFPacking<EF>>; N_COMMITED_CUBES],
) {
    let mut output_layers: [_; 16] =
        array::from_fn(|_| PFPacking::<EF>::zero_vec(input_layers[0].len()));
    let mut cubes: [_; N_COMMITED_CUBES] =
        array::from_fn(|_| PFPacking::<EF>::zero_vec(input_layers[0].len()));
    transposed_par_iter_mut(&mut output_layers)
        .zip(transposed_par_iter_mut(&mut cubes))
        .enumerate()
        .for_each(|(row_index, (output_row, cubes))| {
            let mut buff: [PFPacking<EF>; 16] = array::from_fn(|j| input_layers[j][row_index]);
            for (i, &constant) in rounds.constants.iter().enumerate() {
                *cubes[i] = (buff[0] + constant).cube();
                buff[0] = *cubes[i];
                GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            }
            buff[0] = (buff[0] + rounds.last_constant).cube();
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
            for j in 0..16 {
                *output_row[j] = buff[j];
            }
        });
    (output_layers, cubes)
}

#[instrument(skip_all)]
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

#[instrument(skip_all)]
fn prove_internal_rounds_with_committed_cube(
    prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,
    input_layers: &[Vec<PFPacking<EF>>],
    committed_cubes: &[Vec<PFPacking<EF>>],
    computation: &PartialRoundsWithCommittedCubes,
    claim_point: &[EF],
    output_claims: &[EF],
    selectors: &[DensePolynomial<F>],
) -> (Vec<EF>, Vec<EF>) {
    assert_eq!(input_layers.len(), 16);
    assert_eq!(committed_cubes.len(), N_COMMITED_CUBES);

    let cubes_evals = info_span!("computing cube evals").in_scope(|| {
        committed_cubes
            .par_iter()
            .map(|layer| {
                multivariate_eval::<_, _, _, false>(
                    PFPacking::<EF>::unpack_slice(&layer),
                    &claim_point,
                    selectors,
                )
            })
            .collect::<Vec<EF>>()
    });

    prover_state.add_extension_scalars(&cubes_evals);

    let batching_scalar = prover_state.sample();
    let batched_claim: EF = dot_product(
        output_claims.iter().chain(&cubes_evals).copied(),
        batching_scalar.powers(),
    );
    let batching_scalars_powers = batching_scalar.powers().collect_n(16 + N_COMMITED_CUBES);

    let (sumcheck_point, sumcheck_inner_evals, sumcheck_final_sum) = sumcheck_prove(
        UNIVARIATE_SKIPS,
        MleGroupRef::BasePacked(
            input_layers
                .iter()
                .chain(committed_cubes.iter())
                .map(Vec::as_slice)
                .collect(),
        ),
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
    let batching_scalars_powers = batching_scalar.powers().collect_n(output_claims.len());
    let batched_claim: EF = dot_product(output_claims.iter().copied(), batching_scalar.powers());

    let (retrieved_batched_claim, sumcheck_postponed_claim) = sumcheck_verify_with_univariate_skip(
        verifier_state,
        computation.degree() + 1,
        log_n_poseidons,
        UNIVARIATE_SKIPS,
    )
    .unwrap();

    assert_eq!(retrieved_batched_claim, batched_claim);

    let sumcheck_inner_evals = verifier_state
        .next_extension_scalars_vec(output_claims.len())
        .unwrap();
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

fn multivariate_eval<
    F: Field,
    NF: ExtensionField<F>,
    EF: ExtensionField<F> + ExtensionField<NF>,
    const PARALLEL: bool,
>(
    poly: &[NF],
    point: &[EF],
    selectors: &[DensePolynomial<F>],
) -> EF {
    assert_eq!(poly.len(), 1 << (point.len() + UNIVARIATE_SKIPS - 1));
    selectors
        .iter()
        .zip(poly.chunks_exact(1 << (point.len() - 1)))
        .map(|(selector, chunk)| {
            selector.evaluate(point[0])
                * if PARALLEL {
                    chunk.evaluate(&MultilinearPoint(point[1..].to_vec()))
                } else {
                    chunk.evaluate_sequential(&MultilinearPoint(point[1..].to_vec()))
                }
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
        let mut buff: [NF; 16] = array::from_fn(|j| point[j]);
        if self.first_full_round {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        }
        buff.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + self.constants[j]).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        let mut res = EF::ZERO;
        for i in 0..16 {
            res += alpha_powers[i] * buff[i];
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
        let mut buff: [PFPacking<EF>; 16] = array::from_fn(|j| point[j]);
        if self.first_full_round {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        }
        buff.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + self.constants[j]).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += EFPacking::<EF>::from(alpha_powers[j]) * buff[j];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let mut buff: [EFPacking<EF>; 16] = array::from_fn(|j| point[j]);
        if self.first_full_round {
            GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        }
        buff.iter_mut().enumerate().for_each(|(j, val)| {
            *val = (*val + PFPacking::<EF>::from(self.constants[j])).cube();
        });
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += buff[j] * alpha_powers[j];
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
        let mut buff = [NF::ZERO; 16];
        buff[0] = first_cubed;
        for j in 1..16 {
            buff[j] = point[j];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        let mut res = EF::ZERO;
        for i in 0..16 {
            res += alpha_powers[i] * buff[i];
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
        let mut buff = [PFPacking::<EF>::ZERO; 16];
        buff[0] = first_cubed;
        for j in 1..16 {
            buff[j] = point[j];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += EFPacking::<EF>::from(alpha_powers[j]) * buff[j];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16);
        let first_cubed = (point[0] + PFPacking::<EF>::from(self.constant)).cube();
        let mut buff = [EFPacking::<EF>::ZERO; 16];
        buff[0] = first_cubed;
        for j in 1..16 {
            buff[j] = point[j];
        }
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        let mut res = EFPacking::<EF>::ZERO;
        for j in 0..16 {
            res += buff[j] * alpha_powers[j];
        }
        res
    }
}

pub struct PartialRoundsWithCommittedCubes {
    pub constants: [F; N_COMMITED_CUBES],
    pub last_constant: F,
}

impl<NF: ExtensionField<F>, EF: ExtensionField<NF>> SumcheckComputation<NF, EF>
    for PartialRoundsWithCommittedCubes
{
    fn degree(&self) -> usize {
        3
    }

    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        // points = 16 inputs, then N_COMMITED_CUBES cubes

        debug_assert_eq!(point.len(), 16 + N_COMMITED_CUBES);
        debug_assert_eq!(alpha_powers.len(), 16 + N_COMMITED_CUBES);

        let mut res = EF::ZERO;
        let mut buff: [NF; 16] = array::from_fn(|j| point[j]);
        for (i, &constant) in self.constants.iter().enumerate() {
            let computed_cube = (buff[0] + constant).cube();
            res += alpha_powers[16 + i] * computed_cube;
            buff[0] = point[16 + i]; // commited cube
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        }

        buff[0] = (buff[0] + self.last_constant).cube();
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        for i in 0..16 {
            res += alpha_powers[i] * buff[i];
        }
        res
    }
}

impl SumcheckComputationPacked<EF> for PartialRoundsWithCommittedCubes {
    fn degree(&self) -> usize {
        3
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16 + N_COMMITED_CUBES);
        debug_assert_eq!(alpha_powers.len(), 16 + N_COMMITED_CUBES);

        let mut res = EFPacking::<EF>::ZERO;
        let mut buff: [PFPacking<EF>; 16] = array::from_fn(|j| point[j]);
        for (i, &constant) in self.constants.iter().enumerate() {
            let computed_cube = (buff[0] + constant).cube();
            res += EFPacking::<EF>::from(alpha_powers[16 + i]) * computed_cube;
            buff[0] = point[16 + i]; // commited cube
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        }

        buff[0] = (buff[0] + self.last_constant).cube();
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        for i in 0..16 {
            res += EFPacking::<EF>::from(alpha_powers[i]) * buff[i];
        }
        res
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        debug_assert_eq!(point.len(), 16 + N_COMMITED_CUBES);
        debug_assert_eq!(alpha_powers.len(), 16 + N_COMMITED_CUBES);

        let mut res = EFPacking::<EF>::ZERO;
        let mut buff: [EFPacking<EF>; 16] = array::from_fn(|j| point[j]);
        for (i, &constant) in self.constants.iter().enumerate() {
            let computed_cube = (buff[0] + PFPacking::<EF>::from(constant)).cube();
            res += computed_cube * alpha_powers[16 + i];
            buff[0] = point[16 + i]; // commited cube
            GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        }

        buff[0] = (buff[0] + PFPacking::<EF>::from(self.last_constant)).cube();
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(&mut buff);
        for i in 0..16 {
            res += buff[i] * alpha_powers[i];
        }
        res
    }
}
