// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::ops::{Mul, Sub};

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
        let (prover_data, root) = MerkleData::build(folded_matrix, full);

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

        let folding_randomness = round_state.folding_randomness(self.folding_factor.at_round(round_index));

        let folding_randomness_reversed = {
            let mut v = folding_randomness.0.clone();
            v.reverse();
            MultilinearPoint(v)
        };

        let stir_evaluations: Vec<EF> =
            open_merkle_tree_at_challenges(&round_state.merkle_prover_data, prover_state, &stir_challenges_indexes)
                .iter()
                .map(|answer| answer.evaluate(&folding_randomness_reversed))
                .collect();

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

        round_state.domain_size = new_domain_size;
        round_state.next_domain_gen =
            PF::<EF>::two_adic_generator(log2_strict_usize(new_domain_size) - folding_factor_next);
        round_state.merkle_prover_data = prover_data;

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
    pub(crate) evals: MleOwned<EF>,
    pub(crate) weights: Vec<EF>,
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
    pub(crate) fn run_initial_sumcheck_rounds_svo(
        evals: &MleRef<'_, EF>,
        statement: &[SparseStatement<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        let l = statement[0].total_num_variables;
        let l_0 = folding_factor;

        assert!(
            statement.iter().all(|e| !e.is_next || e.inner_num_variables() >= l_0),
            "next-spill is currently unimplemented",
        );

        let relaxed_statement = relax_eq_spill_statements(statement, l_0);

        let mut sum = build_initial_sum(&relaxed_statement, combination_randomness);

        let unpacked_mle = evals.unpack();
        let unpacked_ref = unpacked_mle.by_ref();
        let f = unpacked_ref
            .as_base()
            .expect("WHIR committed polynomial must be base field");

        let groups = build_all_compressed_groups::<EF>(&relaxed_statement, combination_randomness, f, l, l_0);
        let accs = build_accumulators::<EF>(&groups, l_0);

        let mut challenges: Vec<EF> = Vec::with_capacity(l_0);

        let mut lagrange: Vec<EF> = vec![EF::ONE];
        while challenges.len() < l_0 {
            let r = challenges.len();
            let (c0, c2) = round_message_with_tensor(r, &lagrange, &accs);
            let rho = sumcheck_finish_round(c0, c2, &mut sum, prover_state, pow_bits);
            challenges.push(rho);
            lagrange_tensor_extend(&mut lagrange, rho);
        }

        let evals_ext: Vec<EF> = fold_by_tensor::<EF, _>(f, &challenges);

        let weights = build_post_svo_weights(&relaxed_statement, combination_randomness, &challenges);
        debug_assert_eq!(weights.len(), evals_ext.len());
        let sumcheck = Self {
            evals: MleOwned::Extension(evals_ext),
            weights,
            sum,
        };
        (sumcheck, MultilinearPoint(challenges))
    }
}

fn relax_eq_spill_statements<EF>(statements: &[SparseStatement<EF>], l_0: usize) -> Vec<SparseStatement<EF>>
where
    EF: ExtensionField<PF<EF>>,
{
    let mut out: Vec<SparseStatement<EF>> = Vec::with_capacity(statements.len());
    for smt in statements {
        let m = smt.inner_num_variables();
        if smt.is_next || m >= l_0 {
            out.push(smt.clone());
            continue;
        }
        let l = smt.total_num_variables;
        let extra = l_0 - m;
        let s = l - m;
        debug_assert!(s >= extra);
        for v in &smt.values {
            let top = v.selector >> extra;
            let bot = v.selector & ((1usize << extra) - 1);
            let mut new_point: Vec<EF> = Vec::with_capacity(l_0);
            for k in (0..extra).rev() {
                new_point.push(if (bot >> k) & 1 == 1 { EF::ONE } else { EF::ZERO });
            }
            new_point.extend_from_slice(&smt.point.0);
            out.push(SparseStatement {
                total_num_variables: l,
                point: MultilinearPoint(new_point),
                values: vec![SparseValue {
                    selector: top,
                    value: v.value,
                }],
                is_next: false,
            });
        }
    }
    out
}

fn build_initial_sum<EF>(statements: &[SparseStatement<EF>], gamma: EF) -> EF
where
    EF: ExtensionField<PF<EF>>,
{
    let mut combined_sum = EF::ZERO;
    let mut gamma_pow = EF::ONE;
    for smt in statements {
        for v in &smt.values {
            combined_sum += v.value * gamma_pow;
            gamma_pow *= gamma;
        }
    }
    combined_sum
}

fn build_post_svo_weights<EF>(statements: &[SparseStatement<EF>], gamma: EF, rhos: &[EF]) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    let n = statements[0].total_num_variables;
    let l_0 = rhos.len();
    assert!(l_0 <= n);
    let target_size = 1usize << (n - l_0);
    let mut out = EF::zero_vec(target_size);
    let mut gamma_pow = EF::ONE;

    for smt in statements {
        let m = smt.inner_num_variables();
        let p = &smt.point.0;
        assert!(
            m >= l_0,
            "build_post_svo_weights requires m >= l_0 (pre-relax eq spills)"
        );

        let k = smt.values.len();
        let mut alpha_powers: Vec<EF> = Vec::with_capacity(k);
        for _ in 0..k {
            alpha_powers.push(gamma_pow);
            gamma_pow *= gamma;
        }

        if smt.is_next {
            let mut buf = matrix_next_mle_folded(p);
            for &r in rhos {
                let half = buf.len() / 2;
                buf = (0..half)
                    .into_par_iter()
                    .map(|i| buf[2 * i] + r * (buf[2 * i + 1] - buf[2 * i]))
                    .collect();
            }
            debug_assert_eq!(buf.len(), 1usize << (m - l_0));
            let tail_len = buf.len();
            for (v, &alpha_j) in smt.values.iter().zip(alpha_powers.iter()) {
                let base = v.selector * tail_len;
                let slice = &mut out[base..base + tail_len];
                slice
                    .par_iter_mut()
                    .zip(buf.par_iter())
                    .for_each(|(o, &b)| *o += alpha_j * b);
            }
        } else {
            let mut scalar_eq = EF::ONE;
            for k in 0..l_0 {
                let p_k = p[m - 1 - k];
                let r_k = rhos[k];
                scalar_eq *= p_k * r_k + (EF::ONE - p_k) * (EF::ONE - r_k);
            }
            let tail = &p[..m - l_0];
            let tail_eval: Vec<EF> = if tail.is_empty() {
                vec![scalar_eq]
            } else {
                eval_eq_scaled(tail, scalar_eq)
            };
            let tail_len = tail_eval.len();
            for (v, &alpha_j) in smt.values.iter().zip(alpha_powers.iter()) {
                let base = v.selector * tail_len;
                let slice = &mut out[base..base + tail_len];
                slice
                    .par_iter_mut()
                    .zip(tail_eval.par_iter())
                    .for_each(|(o, &t)| *o += alpha_j * t);
            }
        }
    }

    out
}

#[instrument(skip_all)]
fn build_all_compressed_groups<EF>(
    statement: &[SparseStatement<EF>],
    gamma: EF,
    f: &[PF<EF>],
    l: usize,
    l_0: usize,
) -> Vec<CompressedGroup<EF>>
where
    EF: ExtensionField<PF<EF>>,
{
    let mut groups: Vec<CompressedGroup<EF>> = Vec::new();
    let mut gamma_pow = EF::ONE;
    for smt in statement {
        let s = smt.selector_num_variables();
        assert!(s + l_0 <= l, "build_all_compressed_groups requires s + l_0 <= l");
        let inner_point: Vec<EF> = smt.point.0.clone();
        let sel_bits: Vec<usize> = smt.values.iter().map(|v| v.selector).collect();
        let mut alpha_powers: Vec<EF> = Vec::with_capacity(smt.values.len());
        for _ in 0..smt.values.len() {
            alpha_powers.push(gamma_pow);
            gamma_pow *= gamma;
        }
        if smt.is_next {
            let g = compress_next_claim::<EF>(f, &sel_bits, &inner_point, &alpha_powers, l, l_0, s);
            groups.extend(g);
        } else {
            let g = compress_eq_claim::<EF>(f, &sel_bits, &inner_point, &alpha_powers, l, l_0, s);
            groups.push(g);
        }
    }
    groups
}

fn round_coeffs_flat<EF, E>(evals: &[E], weights: &[EF]) -> (EF, EF)
where
    EF: ExtensionField<PF<EF>> + Mul<E, Output = EF>,
    E: Copy + Send + Sync + Sub<E, Output = E>,
{
    let n = evals.len();
    assert_eq!(n, weights.len());
    assert!(n >= 2 && n.is_power_of_two());
    let half = n / 2;
    (0..half)
        .into_par_iter()
        .map(|i| {
            let lo_e = evals[2 * i];
            let hi_e = evals[2 * i + 1];
            let lo_w = weights[2 * i];
            let hi_w = weights[2 * i + 1];
            // EF on the left so `Mul<E> for EF` is used (Algebra<F> for the base case).
            (lo_w * lo_e, (hi_w - lo_w) * (hi_e - lo_e))
        })
        .reduce(|| (EF::ZERO, EF::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2))
}

fn fold_by_tensor<EF, E>(evals: &[E], rhos: &[EF]) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>> + Mul<E, Output = EF> + From<E>,
    E: Copy + Send + Sync,
{
    let l_0 = rhos.len();
    assert!(evals.len() >= 1 << l_0);
    let width = 1usize << l_0;
    let out_len = evals.len() >> l_0;
    if l_0 == 0 {
        return evals.iter().map(|&v| EF::from(v)).collect();
    }
    let rhos_rev: Vec<EF> = rhos.iter().rev().copied().collect();
    let tensor = eval_eq(&rhos_rev);
    debug_assert_eq!(tensor.len(), width);

    (0..out_len)
        .into_par_iter()
        .map(|j| {
            let offset = j * width;
            let mut acc = EF::ZERO;
            for k in 0..width {
                acc += tensor[k] * evals[offset + k];
            }
            acc
        })
        .collect()
}

fn sumcheck_finish_round<EF: ExtensionField<PF<EF>>>(
    c0: EF,
    c2: EF,
    sum: &mut EF,
    prover_state: &mut impl FSProver<EF>,
    pow_bits: usize,
) -> EF {
    let c1 = *sum - c0.double() - c2;
    let poly = DensePolynomial::new(vec![c0, c1, c2]);
    prover_state.add_sumcheck_polynomial(&poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r: EF = prover_state.sample();
    *sum = poly.evaluate(r);
    r
}

#[instrument(skip_all)]
fn lsb_sumcheck_round<EF: ExtensionField<PF<EF>>>(
    evals: &[EF],
    weights: &[EF],
    sum: &mut EF,
    prover_state: &mut impl FSProver<EF>,
    pow_bits: usize,
) -> EF {
    let (c0, c2) = round_coeffs_flat(evals, weights);
    sumcheck_finish_round(c0, c2, sum, prover_state, pow_bits)
}

/// LSB-fold a slice of evaluations: `out[i] = m[2i] + r * (m[2i+1] - m[2i])`.
fn lsb_fold<EF: ExtensionField<PF<EF>>>(m: &[EF], r: EF) -> Vec<EF> {
    fold_multilinear_lsb(m, r, &|diff, alpha| alpha * diff)
}

#[derive(Debug)]
pub(crate) struct RoundState<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    domain_size: usize,
    next_domain_gen: PF<EF>,
    sumcheck_prover: SumcheckSingle<EF>,
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

        let (sumcheck_prover, folding_randomness) = SumcheckSingle::run_initial_sumcheck_rounds_svo(
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
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    fn folding_randomness(&self, folding_factor: usize) -> MultilinearPoint<EF> {
        MultilinearPoint(self.randomness_vec[self.randomness_vec.len() - folding_factor..].to_vec())
    }
}
