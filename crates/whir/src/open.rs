// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use ::utils::log2_strict_usize;
use fiat_shamir::{FSProver, MerklePath, ProofResult};
use field::{ExtensionField, Field, PackedFieldExtension, PackedValue, TwoAdicField};
use field::{PrimeCharacteristicRing, dot_product};
use poly::*;
use rayon::prelude::*;
use sumcheck::{ProductComputation, sumcheck_prove_many_rounds};
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

    fn validate_witness(&self, witness: &Witness<EF>, polynomial: &MleRef<'_, EF>) -> bool {
        assert_eq!(witness.ood_points.len(), witness.ood_answers.len());
        polynomial.n_vars() == self.num_variables
    }

    #[instrument(name = "WHIR prove", skip_all)]
    pub fn prove(
        &self,
        prover_state: &mut impl FSProver<EF>,
        statement: Evaluation<EF>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> MultilinearPoint<EF> {
        assert!(self.validate_parameters());
        assert!(self.validate_witness(&witness, polynomial));
        assert_eq!(statement.point.len(), self.num_variables);

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

        if round_index == self.n_rounds() {
            return self.final_round(round_index, prover_state, round_state);
        }

        let round_params = &self.round_parameters[round_index];
        let folding_factor_next = self.folding_factor.at_round(round_index + 1);

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
        let (prover_data, root) = MerkleData::build(folded_matrix, full, full);
        prover_state.add_base_scalars(&root);

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

        let stir_evaluations = if let Some(data_b) = &round_state.commitment_merkle_prover_data_b {
            let answers_a =
                open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes);
            let answers_b = open_merkle_tree_at_challenges(data_b, prover_state, &stir_challenges_indexes);
            let mut stir_evaluations = Vec::new();
            for (answer_a, answer_b) in answers_a.iter().zip(&answers_b) {
                let vars_a = answer_a.by_ref().n_vars();
                let vars_b = answer_b.by_ref().n_vars();
                let a_trunc = folding_randomness[1..].to_vec();
                let eval_a = answer_a.evaluate(&MultilinearPoint(a_trunc));
                let b_trunc = folding_randomness[vars_a - vars_b + 1..].to_vec();
                let eval_b = answer_b.evaluate(&MultilinearPoint(b_trunc));
                let last_fold_rand_a = folding_randomness[0];
                let last_fold_rand_b = folding_randomness[..vars_a - vars_b + 1]
                    .iter()
                    .map(|&x| EF::ONE - x)
                    .product::<EF>();
                stir_evaluations.push(eval_a * last_fold_rand_a + eval_b * last_fold_rand_b);
            }
            stir_evaluations
        } else {
            open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes)
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness))
                .collect()
        };

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
            None,
            prover_state,
            folding_factor_next,
            round_params.folding_pow_bits,
        );

        round_state.randomness_vec.extend_from_slice(&next_folding_randomness.0);

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
        let mut coeffs = match &round_state.sumcheck_prover.evals {
            MleOwned::Extension(evals) => evals.clone(),
            MleOwned::ExtensionPacked(evals) => unpack_extension::<EF>(evals),
            _ => unreachable!(),
        };
        evals_to_coeffs(&mut coeffs);
        prover_state.add_extension_scalars(&coeffs);

        prover_state.pow_grinding(self.final_query_pow_bits);

        let final_challenge_indexes = get_challenge_stir_queries(
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

        if self.final_sumcheck_rounds > 0 {
            let final_folding_randomness =
                round_state
                    .sumcheck_prover
                    .run_sumcheck_many_rounds(None, prover_state, self.final_sumcheck_rounds, 0);
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
    pub(crate) evals: MleOwned<EF>,
    pub(crate) weights: MleOwned<EF>,
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
                compute_eval_eq_packed::<_, true>(point, self.weights.as_extension_packed_mut().unwrap(), rand);
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
                compute_eval_eq_base_packed::<_, _, true>(point, self.weights.as_extension_packed_mut().unwrap(), rand);
            });
        self.sum += combination_randomness
            .iter()
            .zip(evaluations.iter())
            .map(|(&rand, &eval)| rand * eval)
            .sum::<EF>();
    }

    fn run_sumcheck_many_rounds(
        &mut self,
        prev_folding_scalar: Option<EF>,
        prover_state: &mut impl FSProver<EF>,
        n_rounds: usize,
        pow_bits: usize,
    ) -> MultilinearPoint<EF> {
        let (challenges, folds, new_sum) = sumcheck_prove_many_rounds(
            MleGroupRef::merge(&[&self.evals.by_ref(), &self.weights.by_ref()]),
            prev_folding_scalar,
            &ProductComputation {},
            &vec![],
            None,
            prover_state,
            self.sum,
            None,
            n_rounds,
            false,
            pow_bits,
        );
        self.sum = new_sum;
        [self.evals, self.weights] = folds.split().try_into().unwrap();
        challenges
    }

    /// SVO + split-eq optimized initial sumcheck with SIMD packing.
    #[instrument(name = "svo_initial_sumcheck", skip_all)]
    pub(crate) fn run_initial_sumcheck_rounds(
        evals: &MleRef<'_, EF>,
        claims: &[Evaluation<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);

        let n_vars = claims[0].point.len();
        let n_claims = claims.len();
        let half = n_vars / 2;
        let n_svo = 1usize << half;
        let n_hi = 1usize << (n_vars - half);

        let mut gamma_pows = vec![EF::ONE; n_claims];
        for i in 1..n_claims {
            gamma_pows[i] = gamma_pows[i - 1] * combination_randomness;
        }
        let sum: EF = claims.iter().zip(&gamma_pows).map(|(c, &gp)| gp * c.value).sum();

        // Packed eq_hi for SIMD accumulator and weight combination
        let eq_his_packed: Vec<Vec<EFPacking<EF>>> = claims.iter().map(|c| eval_eq_packed(&c.point[half..])).collect();
        let mut eq_svos: Vec<Vec<EF>> = claims
            .iter()
            .enumerate()
            .map(|(i, c)| eval_eq_scaled(&c.point[..half], gamma_pows[i]))
            .collect();

        // SIMD-packed accumulator precomputation: A_i[u] = sum_{b_hi} eq_hi_i[b_hi] * f[u * n_hi + b_hi]
        // Parallelize over u (reads f only once), process all claims per u.
        let f = evals.as_base().unwrap();
        let per_u: Vec<Vec<EF>> = (0..n_svo)
            .into_par_iter()
            .map(|u| {
                let f_packed = PFPacking::<EF>::pack_slice(&f[u * n_hi..][..n_hi]);
                (0..n_claims)
                    .map(|ci| {
                        let s: EFPacking<EF> = dot_product(eq_his_packed[ci].iter().copied(), f_packed.iter().copied());
                        EFPacking::<EF>::to_ext_iter([s]).sum()
                    })
                    .collect()
            })
            .collect();
        let mut accumulators: Vec<Vec<EF>> = (0..n_claims)
            .map(|ci| per_u.iter().map(|row| row[ci]).collect())
            .collect();

        // SVO rounds (folding MSB first)
        let mut challenges = Vec::with_capacity(folding_factor);
        let mut current_sum = sum;
        let mut current_n_u = n_svo;

        for _round in 0..folding_factor {
            let half_n_u = current_n_u / 2;
            let mut c0 = EF::ZERO;
            let mut c2 = EF::ZERO;

            for i in 0..n_claims {
                let acc = &accumulators[i];
                let eq = &eq_svos[i];
                for u in 0..half_n_u {
                    c0 += eq[u] * acc[u];
                    c2 += (eq[u + half_n_u] - eq[u]) * (acc[u + half_n_u] - acc[u]);
                }
            }

            let c1 = current_sum - c0 - c0 - c2;
            let poly = DensePolynomial::new(vec![c0, c1, c2]);
            prover_state.add_sumcheck_polynomial(&poly.coeffs, None);
            prover_state.pow_grinding(pow_bits);
            let challenge: EF = prover_state.sample();
            challenges.push(challenge);
            current_sum = poly.evaluate(challenge);

            current_n_u = half_n_u;
            for i in 0..n_claims {
                fold_msb_in_place(&mut accumulators[i], current_n_u, challenge);
                fold_msb_in_place(&mut eq_svos[i], current_n_u, challenge);
            }
        }

        // SIMD-packed multi-fold: iterate eq outer, packed saxpy inner.
        let eq_at_challenges = eval_eq(&challenges);
        let n_svo_orig = 1usize << folding_factor;
        let n_rest = 1usize << (n_vars - folding_factor);
        let n_rest_packed = n_rest >> packing_log_width::<EF>();
        let mut out_packed = EFPacking::<EF>::zero_vec(n_rest_packed);
        for u in 0..n_svo_orig {
            let coeff = EFPacking::<EF>::from(eq_at_challenges[u]);
            let f_row_packed = PFPacking::<EF>::pack_slice(&f[u * n_rest..][..n_rest]);
            out_packed
                .par_iter_mut()
                .zip(f_row_packed.par_iter())
                .for_each(|(dest, &fv)| *dest += coeff * fv);
        }

        // SIMD-packed weight combination
        let n_u_rem = 1usize << (half - folding_factor);
        let n_hi_packed = n_hi >> packing_log_width::<EF>();
        let mut w_packed = EFPacking::<EF>::zero_vec(n_rest_packed);
        for i in 0..n_claims {
            for u_rem in 0..n_u_rem {
                let scale = eq_svos[i][u_rem]; // already includes gamma
                let dst = &mut w_packed[u_rem * n_hi_packed..][..n_hi_packed];
                for (d, &eq_v) in dst.iter_mut().zip(&eq_his_packed[i]) {
                    *d += eq_v * scale;
                }
            }
        }

        let sumcheck = Self {
            evals: MleOwned::ExtensionPacked(out_packed),
            weights: MleOwned::ExtensionPacked(w_packed),
            sum: current_sum,
        };

        (sumcheck, MultilinearPoint(challenges))
    }
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
        dense_claim: Evaluation<EF>,
        witness: Witness<EF>,
        polynomial: &MleRef<'_, EF>,
    ) -> ProofResult<Self> {
        let mut claims: Vec<Evaluation<EF>> = witness
            .ood_points
            .into_iter()
            .zip(witness.ood_answers)
            .map(|(point, value)| {
                Evaluation::new(
                    MultilinearPoint::expand_from_univariate(point, prover.num_variables),
                    value,
                )
            })
            .collect();
        claims.push(dense_claim);

        let combination_randomness_gen: EF = prover_state.sample();

        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds(
            polynomial,
            &claims,
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

fn fold_msb_in_place<EF: Field>(v: &mut Vec<EF>, half: usize, r: EF) {
    for i in 0..half {
        v[i] = v[i] + r * (v[i + half] - v[i]);
    }
    v.truncate(half);
}
