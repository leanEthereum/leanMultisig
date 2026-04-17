// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use ::utils::log2_strict_usize;
use fiat_shamir::{FSProver, MerklePath, ProofResult};
use field::PrimeCharacteristicRing;
use field::{ExtensionField, Field, TwoAdicField};
use poly::*;
use rayon::prelude::*;
use tracing::{info_span, instrument};

use crate::{config::WhirConfig, *};

impl<EF> WhirConfig<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    fn validate_parameters(&self) -> bool {
        self.num_variables == self.folding_factor.total_number(self.n_rounds()) + self.final_sumcheck_rounds
    }

    fn validate_statement(&self, statement: &[SparseStatement<EF>]) {
        statement.iter().for_each(|e| {
            assert_eq!(e.total_num_variables, self.num_variables);
            assert!(!e.values.is_empty());
            assert!(e.values.iter().all(|v| v.selector < 1 << e.selector_num_variables()));
        });
    }

    fn validate_witness(&self, witness: &Witness<EF>, polynomial: &MleRef<'_, EF>) -> bool {
        assert_eq!(witness.ood_points.len(), witness.ood_answers.len());
        polynomial.n_vars() == self.num_variables
    }

    #[instrument(name = "WHIR prove", skip_all)]
    pub fn prove(
        &self,
        prover_state: &mut impl FSProver<EF>,
        statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.validate_witness(&witness, polynomial));
        self.validate_statement(&statement);

        let mut round_state =
            RoundState::initialize_first_round_state(self, prover_state, statement, witness, polynomial).unwrap();

        for round in 0..=self.n_rounds() {
            self.round(round, prover_state, &mut round_state).unwrap();
        }

        MultilinearPoint(round_state.randomness_vec)
    }

    fn round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        let folded_evaluations = &round_state.sumcheck_prover.evals;
        let num_variables = self.num_variables - self.folding_factor.total_number(round_index);

        // Base case: final round reached
        if round_index == self.n_rounds() {
            return self.final_round(round_index, prover_state, round_state);
        }

        let round_params = &self.round_parameters[round_index];

        // Compute the folding factors for later use
        let folding_factor_next = self.folding_factor.at_round(round_index + 1);

        // Compute polynomial evaluations and build Merkle tree
        let domain_reduction = 1 << self.rs_reduction_factor(round_index);
        let new_domain_size = round_state.domain_size / domain_reduction;
        let inv_rate = new_domain_size >> num_variables;
        let folded_matrix = info_span!("FFT").in_scope(|| {
            reorder_and_dft(
                &folded_evaluations.by_ref(),
                folding_factor_next,
                log2_strict_usize(inv_rate),
                1 << folding_factor_next,
            )
        });

        let full = 1 << folding_factor_next;
        let (prover_data, root) = MerkleData::build(folded_matrix, full);

        prover_state.add_base_scalars(&root);

        // Handle OOD (Out-Of-Domain) samples
        let (ood_points, ood_answers) =
            sample_ood_points::<EF, _>(prover_state, round_params.ood_samples, num_variables, |point| {
                info_span!("ood evaluation").in_scope(|| folded_evaluations.evaluate(point))
            });

        prover_state.pow_grinding(round_params.query_pow_bits);

        let (ood_challenges, stir_challenges, stir_challenges_indexes) = self.compute_stir_queries(
            prover_state,
            round_state,
            num_variables,
            round_params,
            &ood_points,
            round_index,
        )?;

        let folding_randomness = round_state.folding_randomness(
            self.folding_factor.at_round(round_index) + round_state.commitment_merkle_prover_data_b.is_some() as usize,
        );

        // LSB-fold WHIR: the leaf vars are the polynomial's last k vars (matrix LSB-cols), so
        // evaluate needs the per-round challenges reversed.
        let folding_randomness_reversed = {
            let mut v = folding_randomness.0.clone();
            v.reverse();
            MultilinearPoint(v)
        };

        if round_state.commitment_merkle_prover_data_b.is_some() {
            // NOTE: the data_b path is unused in current WHIR (only the single-commitment path
            // is exercised). Left untouched; would need its own LSB-fold-aware reversal logic.
            unimplemented!("LSB-fold WHIR does not yet handle the data_b commitment path");
        }
        let stir_evaluations: Vec<EF> =
            open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes)
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness_reversed))
                .collect();

        // Randomness for combination
        let combination_randomness_gen: EF = prover_state.sample();
        let ood_combination_randomness: Vec<_> = combination_randomness_gen.powers().collect_n(ood_challenges.len());
        round_state
            .sumcheck_prover
            .add_new_equality(&ood_challenges, &ood_answers, &ood_combination_randomness);
        let stir_combination_randomness = combination_randomness_gen
            .powers()
            .skip(ood_challenges.len())
            .take(stir_challenges.len())
            .collect::<Vec<_>>();

        round_state.sumcheck_prover.add_new_base_equality(
            &stir_challenges,
            &stir_evaluations,
            &stir_combination_randomness,
        );

        let next_folding_randomness = round_state.sumcheck_prover.run_sumcheck_many_rounds(
            prover_state,
            folding_factor_next,
            round_params.folding_pow_bits,
        );

        round_state.randomness_vec.extend_from_slice(&next_folding_randomness.0);

        // Update round state
        round_state.domain_size = new_domain_size;
        round_state.next_domain_gen =
            PF::<EF>::two_adic_generator(log2_strict_usize(new_domain_size) - folding_factor_next);
        round_state.merkle_prover_data = prover_data;
        round_state.commitment_merkle_prover_data_b = None;

        Ok(())
    }

    fn final_round(
        &self,
        round_index: usize,
        prover_state: &mut impl FSProver<EF>,
        round_state: &mut RoundState<EF>,
    ) -> ProofResult<()> {
        // Convert evaluations to coefficient form and send to the verifier.
        let mut coeffs = round_state
            .sumcheck_prover
            .evals
            .as_extension()
            .expect("WHIR sumcheck stores evals as extension")
            .to_vec();
        evals_to_coeffs(&mut coeffs);
        prover_state.add_extension_scalars(&coeffs);

        prover_state.pow_grinding(self.final_query_pow_bits);

        // Final verifier queries and answers. The indices are over the folded domain.
        let final_challenge_indexes = get_challenge_stir_queries(
            // The size of the original domain before folding
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            self.final_queries,
            prover_state,
        );

        let mut base_paths = Vec::new();
        let mut ext_paths = Vec::new();
        for challenge in final_challenge_indexes {
            let (answer, sibling_hashes) = round_state.merkle_prover_data.open(challenge);

            match answer {
                MleOwned::Base(leaf) => {
                    base_paths.push(MerklePath {
                        leaf_data: leaf,
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                MleOwned::Extension(leaf) => {
                    ext_paths.push(MerklePath {
                        leaf_data: leaf,
                        sibling_hashes,
                        leaf_index: challenge,
                    });
                }
                _ => unreachable!(),
            }
        }
        if !base_paths.is_empty() {
            prover_state.hint_merkle_paths_base(base_paths);
        }
        if !ext_paths.is_empty() {
            prover_state.hint_merkle_paths_extension(ext_paths);
        }

        // Run final sumcheck if required
        if self.final_sumcheck_rounds > 0 {
            let final_folding_randomness =
                round_state
                    .sumcheck_prover
                    .run_sumcheck_many_rounds(prover_state, self.final_sumcheck_rounds, 0);

            round_state.randomness_vec.extend(final_folding_randomness.0);
        }

        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn compute_stir_queries(
        &self,
        prover_state: &mut impl FSProver<EF>,
        round_state: &RoundState<EF>,
        num_variables: usize,
        round_params: &RoundConfig<EF>,
        ood_points: &[EF],
        round_index: usize,
    ) -> ProofResult<(Vec<MultilinearPoint<EF>>, Vec<MultilinearPoint<PF<EF>>>, Vec<usize>)> {
        let stir_challenges_indexes = get_challenge_stir_queries(
            round_state.domain_size >> self.folding_factor.at_round(round_index),
            round_params.num_queries,
            prover_state,
        );

        let domain_scaled_gen = round_state.next_domain_gen;
        let ood_challenges = ood_points
            .iter()
            .map(|univariate| MultilinearPoint::expand_from_univariate(*univariate, num_variables))
            .collect();
        let stir_challenges = stir_challenges_indexes
            .iter()
            .map(|i| MultilinearPoint::expand_from_univariate(domain_scaled_gen.exp_u64(*i as u64), num_variables))
            .collect();

        Ok((ood_challenges, stir_challenges, stir_challenges_indexes))
    }
}

fn open_merkle_tree_at_challenges<EF: ExtensionField<PF<EF>>>(
    merkle_tree: &MerkleData<EF>,
    prover_state: &mut impl FSProver<EF>,
    stir_challenges_indexes: &[usize],
) -> Vec<MleOwned<EF>> {
    let mut answers = Vec::new();
    let mut base_paths = Vec::new();
    let mut ext_paths = Vec::new();

    for &challenge in stir_challenges_indexes {
        let (answer, sibling_hashes) = merkle_tree.open(challenge);

        match &answer {
            MleOwned::Base(leaf) => {
                base_paths.push(MerklePath {
                    leaf_data: leaf.clone(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            MleOwned::Extension(leaf) => {
                ext_paths.push(MerklePath {
                    leaf_data: leaf.clone(),
                    sibling_hashes,
                    leaf_index: challenge,
                });
            }
            _ => unreachable!(),
        }
        answers.push(answer);
    }

    if !base_paths.is_empty() {
        prover_state.hint_merkle_paths_base(base_paths);
    }
    if !ext_paths.is_empty() {
        prover_state.hint_merkle_paths_extension(ext_paths);
    }

    answers
}

#[derive(Debug, Clone)]
pub struct SumcheckSingle<EF: ExtensionField<PF<EF>>> {
    /// Evaluations of the polynomial `p(X)` (extension, unpacked).
    pub(crate) evals: MleOwned<EF>,
    /// Evaluations of the equality polynomial used for enforcing constraints.
    pub(crate) weights: Vec<EF>,
    /// Accumulated sum incorporating equality constraints.
    pub(crate) sum: EF,
}

impl<EF: Field> SumcheckSingle<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    #[instrument(skip_all)]
    pub(crate) fn add_new_equality(
        &mut self,
        points: &[MultilinearPoint<EF>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        points
            .iter()
            .zip(combination_randomness.iter())
            .for_each(|(point, &rand)| {
                compute_eval_eq::<PF<EF>, EF, true>(&point.0, &mut self.weights, rand);
            });

        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    #[instrument(skip_all)]
    pub(crate) fn add_new_base_equality(
        &mut self,
        points: &[MultilinearPoint<PF<EF>>],
        evaluations: &[EF],
        combination_randomness: &[EF],
    ) {
        assert_eq!(combination_randomness.len(), points.len());
        assert_eq!(evaluations.len(), points.len());

        points
            .iter()
            .zip(combination_randomness.iter())
            .for_each(|(point, &rand)| {
                compute_eval_eq_base::<PF<EF>, EF, true>(&point.0, &mut self.weights, rand);
            });

        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    /// LSB-fold sumcheck: each round folds bit 0 of the eval/weight indices.
    /// No SIMD packing — operates on plain `Vec<EF>`.
    fn run_sumcheck_many_rounds(
        &mut self,
        prover_state: &mut impl FSProver<EF>,
        n_rounds: usize,
        pow_bits: usize,
    ) -> MultilinearPoint<EF> {
        let mut challenges = Vec::with_capacity(n_rounds);
        for _ in 0..n_rounds {
            let r = lsb_sumcheck_round(
                self.evals.as_extension().expect("WHIR sumcheck operates on Vec<EF>"),
                &self.weights,
                &mut self.sum,
                prover_state,
                pow_bits,
            );
            challenges.push(r);

            let evals_ref = self.evals.as_extension().unwrap();
            let new_evals = lsb_fold(evals_ref, r);
            let new_weights = lsb_fold(&self.weights, r);
            self.evals = MleOwned::Extension(new_evals);
            self.weights = new_weights;
        }
        MultilinearPoint(challenges)
    }

    #[instrument(skip_all)]
    pub(crate) fn run_initial_sumcheck_rounds(
        evals: &MleRef<'_, EF>,
        statement: &[SparseStatement<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);

        let (mut weights, mut sum) = combine_statement::<EF>(statement, combination_randomness);

        // Materialize evals as a plain Vec<EF>: WHIR sumcheck has no SIMD path.
        let mut evals_ext: Vec<EF> = evals.unpack().by_ref().clone_to_owned().into_extension().unwrap_or_else(|| {
            // If the polynomial is base, lift to extension element-by-element.
            evals
                .unpack()
                .by_ref()
                .as_base()
                .expect("WHIR sumcheck input must be base or extension (no packed)")
                .iter()
                .map(|&v| EF::from(v))
                .collect()
        });

        let mut challenges = Vec::with_capacity(folding_factor);
        for _ in 0..folding_factor {
            let r = lsb_sumcheck_round(&evals_ext, &weights, &mut sum, prover_state, pow_bits);
            challenges.push(r);
            evals_ext = lsb_fold(&evals_ext, r);
            weights = lsb_fold(&weights, r);
        }

        let sumcheck = Self {
            evals: MleOwned::Extension(evals_ext),
            weights,
            sum,
        };

        (sumcheck, MultilinearPoint(challenges))
    }
}

/// Compute one LSB-fold sumcheck round for the product `evals * weights`,
/// send the round polynomial, sample a challenge, and update `sum` to its evaluation at the challenge.
#[instrument(skip_all)]
fn lsb_sumcheck_round<EF: ExtensionField<PF<EF>>>(
    evals: &[EF],
    weights: &[EF],
    sum: &mut EF,
    prover_state: &mut impl FSProver<EF>,
    pow_bits: usize,
) -> EF {
    let n = evals.len();
    assert_eq!(n, weights.len());
    assert!(n >= 2 && n.is_power_of_two());
    let half = n / 2;

    // For LSB-fold: lo = evals[2i], hi = evals[2i+1]. Same for weights.
    // Round polynomial p(z) = c0 + c1*z + c2*z^2 with
    //   p(0) = sum_i lo_e * lo_w                         = c0
    //   p(2) - 2*p(1) + p(0) = c2 (second difference)
    // We compute c0 directly and c2 = sum_i (hi_e - lo_e) * (hi_w - lo_w).
    // Then c1 = sum_prev - 2*c0 - c2 (from the standard sumcheck identity).
    let (c0, c2) = (0..half)
        .into_par_iter()
        .map(|i| {
            let lo_e = evals[2 * i];
            let hi_e = evals[2 * i + 1];
            let lo_w = weights[2 * i];
            let hi_w = weights[2 * i + 1];
            (lo_e * lo_w, (hi_e - lo_e) * (hi_w - lo_w))
        })
        .reduce(|| (EF::ZERO, EF::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2));

    let c1 = *sum - c0.double() - c2;
    let poly = DensePolynomial::new(vec![c0, c1, c2]);
    prover_state.add_sumcheck_polynomial(&poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r: EF = prover_state.sample();
    *sum = poly.evaluate(r);
    r
}

/// LSB-fold a slice of evaluations: `out[i] = m[2i] + r * (m[2i+1] - m[2i])`.
fn lsb_fold<EF: ExtensionField<PF<EF>>>(m: &[EF], r: EF) -> Vec<EF> {
    let half = m.len() / 2;
    (0..half).into_par_iter().map(|i| m[2 * i] + r * (m[2 * i + 1] - m[2 * i])).collect()
}

#[derive(Debug)]
pub(crate) struct RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    domain_size: usize,
    next_domain_gen: PF<EF>,
    sumcheck_prover: SumcheckSingle<EF>,
    commitment_merkle_prover_data_b: Option<MerkleData<EF>>,
    merkle_prover_data: MerkleData<EF>,
    randomness_vec: Vec<EF>,
}

#[allow(clippy::mismatching_type_param_order)]
impl<EF> RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
    PF<EF>: TwoAdicField,
{
    pub(crate) fn initialize_first_round_state(
        prover: &WhirConfig<EF>,
        prover_state: &mut impl FSProver<EF>,
        mut statement: Vec<SparseStatement<EF>>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> ProofResult<Self> {
        let ood_statements = witness
            .ood_points
            .into_iter()
            .zip(witness.ood_answers)
            .map(|(point, evaluation)| {
                SparseStatement::dense(
                    MultilinearPoint::expand_from_univariate(point, prover.num_variables),
                    evaluation,
                )
            })
            .collect::<Vec<_>>();

        statement.splice(0..0, ood_statements);

        let combination_randomness_gen: EF = prover_state.sample();

        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds(
            polynomial,
            &statement,
            combination_randomness_gen,
            prover_state,
            prover.folding_factor.at_round(0),
            prover.starting_folding_pow_bits,
        );

        Ok(Self {
            domain_size: prover.starting_domain_size(),
            next_domain_gen: PF::<EF>::two_adic_generator(
                log2_strict_usize(prover.starting_domain_size()) - prover.folding_factor.at_round(0),
            ),
            sumcheck_prover,
            merkle_prover_data: witness.prover_data,
            commitment_merkle_prover_data_b: None,
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    fn folding_randomness(&self, folding_factor: usize) -> MultilinearPoint<EF> {
        MultilinearPoint(self.randomness_vec[self.randomness_vec.len() - folding_factor..].to_vec())
    }
}

#[instrument(skip_all, fields(num_constraints = statements.len(), n_vars = statements[0].total_num_variables))]
fn combine_statement<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> (Vec<EF>, EF)
where
    EF: ExtensionField<PF<EF>>,
{
    let num_variables = statements[0].total_num_variables;
    assert!(statements.iter().all(|e| e.total_num_variables == num_variables));

    let mut combined_weights = EF::zero_vec(1 << num_variables);

    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;

    for smt in statements {
        if !smt.is_next && smt.values.len() == 1 {
            for evaluation in &smt.values {
                compute_sparse_eval_eq::<EF>(evaluation.selector, &smt.point.0, &mut combined_weights, gamma_pow);
                combined_sum += evaluation.value * gamma_pow;
                gamma_pow *= gamma;
            }
        } else {
            let inner_poly: Vec<EF> = if smt.is_next {
                matrix_next_mle_folded(&smt.point.0)
            } else {
                eval_eq(&smt.point.0)
            };
            let shift = smt.inner_num_variables();
            let mut indexed_smt_values = smt.values.iter().enumerate().collect::<Vec<_>>();
            indexed_smt_values.sort_by_key(|(_, e)| e.selector);
            indexed_smt_values.dedup_by_key(|(_, e)| e.selector);
            assert_eq!(
                indexed_smt_values.len(),
                smt.values.len(),
                "Duplicate selectors in sparse statement"
            );
            let mut chunks_mut = split_at_mut_many(
                &mut combined_weights,
                &indexed_smt_values
                    .iter()
                    .map(|(_, e)| e.selector << shift)
                    .collect::<Vec<_>>(),
            );
            chunks_mut.remove(0);
            let mut next_gamma_powers = vec![gamma_pow];
            for _ in 1..indexed_smt_values.len() {
                next_gamma_powers.push(*next_gamma_powers.last().unwrap() * gamma);
            }
            for (e, &scalar) in smt.values.iter().zip(&next_gamma_powers) {
                combined_sum += e.value * scalar;
            }
            chunks_mut
                .into_par_iter()
                .zip(&indexed_smt_values)
                .for_each(|(out_buff, &(origin_index, _))| {
                    out_buff[..1 << shift]
                        .par_iter_mut()
                        .zip(&inner_poly)
                        .for_each(|(out_elem, &poly_elem)| {
                            *out_elem += poly_elem * next_gamma_powers[origin_index];
                        });
                });
            gamma_pow = *next_gamma_powers.last().unwrap() * gamma;
        }
    }

    (combined_weights, combined_sum)
}
