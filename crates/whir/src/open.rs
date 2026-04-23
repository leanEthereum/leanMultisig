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

        // Build the structured weight polynomial without materializing a 2^n flat buffer.
        // Dense claims (m_g == n_total_vars) go into a shared 2^n buffer inside `SplitWeights`;
        // sparse claims stay factored as `(inner_eq, select_coefs)` pairs until they either
        // collapse to scalar phase or reach the collapse point after `folding_factor` rounds.
        let (mut split, mut sum) = SplitWeights::<EF>::from_statements(statement, combination_randomness);

        // Unpack the input MLE. `.unpack()` is zero-copy for base-field inputs (including
        // SIMD-packed base) — it reinterprets the underlying slice — and allocates only when
        // converting extension-packed → extension. Keep the unpacked form alive for the round-0
        // borrow below.
        let unpacked_mle = evals.unpack();
        let unpacked_ref = unpacked_mle.by_ref();

        let mut challenges = Vec::with_capacity(folding_factor);
        // Round-0 specialization: if `evals` is base-field, stay in F until the first fold.
        // This avoids both the 2^n EF-lift allocation and the EF·EF arithmetic on the largest
        // round. For EF5/KoalaBear the per-element product is ~5× cheaper and the temporary
        // buffer is ~5× smaller. Committed polynomials are typically base-field so this path
        // is the common one.
        let mut evals_ext: Vec<EF> = if let Some(base) = unpacked_ref.as_base() {
            let r = lsb_sumcheck_round_split_base(base, &split, &mut sum, prover_state, pow_bits);
            challenges.push(r);
            split.fold(r);
            lsb_fold_base_to_ext(base, r)
        } else {
            // Extension input: materialize as Vec<EF> and take the standard path below for all
            // `folding_factor` rounds.
            unpacked_ref
                .as_extension()
                .expect("WHIR sumcheck input must be base or extension (no packed)")
                .to_vec()
        };

        while challenges.len() < folding_factor {
            let r = lsb_sumcheck_round_split(&evals_ext, &split, &mut sum, prover_state, pow_bits);
            challenges.push(r);
            evals_ext = lsb_fold(&evals_ext, r);
            split.fold(r);
        }

        // Collapse the structured rep to a flat `Vec<EF>` matching the current folded size so
        // the rest of the prover (add_new_equality, run_sumcheck_many_rounds) operates on a
        // plain weight vector exactly as before. After `folding_factor` folds the size is
        // `2^(n - folding_factor)` ≈ 10 MB for n = 26 — fine to materialize.
        let weights = split.into_flat(evals_ext.len());

        let sumcheck = Self {
            evals: MleOwned::Extension(evals_ext),
            weights,
            sum,
        };

        (sumcheck, MultilinearPoint(challenges))
    }

    /// SVO + split-eq variant of [`Self::run_initial_sumcheck_rounds`]. Replaces
    /// the per-round `(c0, c2)` scan over the weight polynomial with a ternary
    /// accumulator pipeline (see `svo.rs` / `misc/whir_sumcheck.tex`). The
    /// Fiat-Shamir transcript is byte-identical to the flat path: same
    /// `(c0, c1, c2)` values in the same order, so the verifier is
    /// unaffected.
    ///
    /// Falls back to [`Self::run_initial_sumcheck_rounds`] if any statement
    /// violates the selector-inside-split assumption `s_g <= l - l_0` (the
    /// sparse-group spill regime).
    #[instrument(skip_all)]
    pub(crate) fn run_initial_sumcheck_rounds_svo(
        evals: &MleRef<'_, EF>,
        statement: &[SparseStatement<EF>],
        combination_randomness: EF,
        prover_state: &mut impl FSProver<EF>,
        folding_factor: usize,
        pow_bits: usize,
    ) -> (Self, MultilinearPoint<EF>) {
        assert_ne!(folding_factor, 0);
        let l = statement[0].total_num_variables;
        let l_0 = folding_factor;

        // Eq-claims: any `s` is fine (non-spill for `s <= l - l_0`, spill
        // fallback via [`compress_eq_spill_claim`] otherwise).
        // Next-claims: require `m >= l_0` (the bucketed algorithm's
        // geometric picture needs a non-empty svo block inside the inner
        // point). Fall back to the structured flat path if any next-claim
        // violates this.
        let svo_ok = statement.iter().all(|e| !e.is_next || e.inner_num_variables() >= l_0);
        if !svo_ok {
            return Self::run_initial_sumcheck_rounds(
                evals,
                statement,
                combination_randomness,
                prover_state,
                folding_factor,
                pow_bits,
            );
        }

        // Phase 3: compute the initial running sum directly from the
        // statements (Σ γ^i · value_i) — we do not need the structured
        // `SplitWeights` representation during the SVO rounds. The post-SVO
        // weight vector is built once, at the end, via
        // [`build_post_svo_weights`].
        let mut sum = build_initial_sum(statement, combination_randomness);

        // Unpack evals (zero-copy for base) and build CompressedGroups.
        let unpacked_mle = evals.unpack();
        let unpacked_ref = unpacked_mle.by_ref();
        let f_base_opt = unpacked_ref.as_base();
        let f_ext_opt = unpacked_ref.as_extension();
        let f = match (f_base_opt, f_ext_opt) {
            (Some(b), _) => crate::svo::FEvals::Base(b),
            (None, Some(e)) => crate::svo::FEvals::Ext(e),
            _ => panic!("WHIR sumcheck input must be base or extension (no packed)"),
        };

        let groups = build_all_compressed_groups::<EF>(statement, combination_randomness, f, l, l_0);
        let accs = build_accumulators::<EF>(&groups, l_0);

        let mut challenges: Vec<EF> = Vec::with_capacity(l_0);

        // Run all l_0 SVO rounds using only the accumulator pipeline — no
        // per-round fold of `f`. Challenges are collected in natural sampling
        // order (ρ_0, ρ_1, .., ρ_{l_0 - 1}). A persistent Lagrange tensor is
        // extended once per round instead of rebuilt from scratch.
        let mut lagrange: Vec<EF> = vec![EF::ONE];
        while challenges.len() < l_0 {
            let r = challenges.len();
            let (h0, h1, h2) = round_message_with_tensor(r, &lagrange, &accs);
            let (c0, c2) = values_to_coeffs(h0, h1, h2);
            let rho = sumcheck_finish_round(c0, c2, &mut sum, prover_state, pow_bits);
            challenges.push(rho);
            lagrange_tensor_extend(&mut lagrange, rho);
        }

        // Single-pass tensor fold of `f` down to size 2^{l - l_0}. Base-field
        // input stays at `EF · F` cost per multiply (instead of promoting to
        // EF after round 0, which would force `EF · EF` on subsequent rounds).
        let evals_ext: Vec<EF> = if let Some(base) = f_base_opt {
            fold_by_tensor::<EF, _>(base, &challenges)
        } else {
            let ext = f_ext_opt.expect("WHIR sumcheck input must be base or extension (no packed)");
            fold_by_tensor::<EF, _>(ext, &challenges)
        };

        let weights = build_post_svo_weights(statement, combination_randomness, &challenges);
        debug_assert_eq!(weights.len(), evals_ext.len());
        let sumcheck = Self {
            evals: MleOwned::Extension(evals_ext),
            weights,
            sum,
        };
        (sumcheck, MultilinearPoint(challenges))
    }
}

/// Initial running sum `Σ γ^i · value_i` matching
/// [`SplitWeights::from_statements`]'s `combined_sum` output.
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

/// Build the post-SVO weight vector of size `2^{n - l_0}` directly from the
/// sparse statements and the sampled `rhos = (ρ_0, .., ρ_{l_0 - 1})`.
///
/// Equivalent to `SplitWeights::from_statements(statement, γ).fold(ρ_0)...
/// .fold(ρ_{l_0-1}).into_flat(2^{n - l_0})`, but skips the per-round
/// `Θ(2^{n - r})` fold of the dense buffer (see Phase 3 in
/// `whir_sumcheck_optim.md`).
///
/// For each statement group, the contribution to the post-SVO weight slice at
/// selector `sel_j` is:
/// - **eq, `m >= l_0`:** `α_j · scalar_eq · eval_eq(p[..m - l_0])` where
///   `scalar_eq = Π_{k=0}^{l_0 - 1} eq(p[m - 1 - k], ρ_k)`.
/// - **eq, `m < l_0` (spill):** a single scalar deposited at residual index
///   `sel_j >> (l_0 - m)`, scaled by the inner and spill eq factors.
/// - **nxt, `m >= l_0`:** `α_j · next_folded`, where `next_folded` is
///   `matrix_next_mle_folded(p)` folded `l_0` times by the `ρ`s.
///
/// Panics for `nxt` with `m < l_0` — this is the eligibility precondition of
/// the SVO path.
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

        let k = smt.values.len();
        let mut alpha_powers: Vec<EF> = Vec::with_capacity(k);
        for _ in 0..k {
            alpha_powers.push(gamma_pow);
            gamma_pow *= gamma;
        }

        if m >= l_0 {
            if smt.is_next {
                // Materialize and fold `l_0` times. The dense `2^n` OOD buffer
                // is never folded — the nxt inner poly has size `2^m ≤ 2^n`.
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
                    let sel_j = v.selector;
                    let base = sel_j * tail_len;
                    let slice = &mut out[base..base + tail_len];
                    slice
                        .par_iter_mut()
                        .zip(buf.par_iter())
                        .for_each(|(o, &b)| *o += alpha_j * b);
                }
            } else {
                // scalar_eq = Π_{k=0}^{l_0-1} eq(p[m-1-k], ρ_k).
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
                    let sel_j = v.selector;
                    let base = sel_j * tail_len;
                    let slice = &mut out[base..base + tail_len];
                    slice
                        .par_iter_mut()
                        .zip(tail_eval.par_iter())
                        .for_each(|(o, &t)| *o += alpha_j * t);
                }
            }
        } else {
            // Spill regime: m < l_0 (and !is_next, enforced above).
            assert!(!smt.is_next, "nxt spill not supported in SVO path");
            // Inner-phase folds (m of them) fix the last m coords of `p`:
            //   inner_scalar = Π_{i=0}^{m-1} eq(p[m - 1 - i], ρ_i).
            let mut inner_scalar = EF::ONE;
            for i in 0..m {
                let p_i = p[m - 1 - i];
                let r_i = rhos[i];
                inner_scalar *= p_i * r_i + (EF::ONE - p_i) * (EF::ONE - r_i);
            }
            // Scalar-phase folds (l_0 - m of them) collapse `sel_j` one LSB at
            // a time; bit k of the original `sel_j` is folded at round `m + k`
            // with scalar `(1 - ρ_{m+k})` if the bit is 0 else `ρ_{m+k}`.
            for (v, &alpha_j) in smt.values.iter().zip(alpha_powers.iter()) {
                let mut spill_scalar = EF::ONE;
                let mut sel_rem = v.selector;
                for k in 0..(l_0 - m) {
                    let r_k = rhos[m + k];
                    let bit = sel_rem & 1;
                    spill_scalar *= if bit == 0 { EF::ONE - r_k } else { r_k };
                    sel_rem >>= 1;
                }
                out[sel_rem] += alpha_j * inner_scalar * spill_scalar;
            }
        }
    }

    out
}

/// Translate `SparseStatement`s into SVO-ready `CompressedGroup`s, preserving
/// the per-claim `gamma`-power order of [`SplitWeights::from_statements`] (so
/// the `(c0, c2)` output of the two paths matches exactly).
fn build_all_compressed_groups<EF>(
    statement: &[SparseStatement<EF>],
    gamma: EF,
    f: crate::svo::FEvals<'_, EF>,
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
        let inner_point: Vec<EF> = smt.point.0.clone();
        let sel_bits: Vec<usize> = smt.values.iter().map(|v| v.selector).collect();
        let mut alpha_powers: Vec<EF> = Vec::with_capacity(smt.values.len());
        for _ in 0..smt.values.len() {
            alpha_powers.push(gamma_pow);
            gamma_pow *= gamma;
        }
        if smt.is_next {
            let g = compress_next_claim_bucketed::<EF>(f, &sel_bits, &inner_point, &alpha_powers, l, l_0, s);
            groups.extend(g);
        } else if s + l_0 <= l {
            let g = compress_eq_claim::<EF>(f, &sel_bits, &inner_point, &alpha_powers, l, l_0, s);
            groups.push(g);
        } else {
            // Eq-claim spill regime: one CompressedGroup per claim.
            let g = compress_eq_spill_claim::<EF>(f, &sel_bits, &inner_point, &alpha_powers, l, l_0, s);
            groups.extend(g);
        }
    }
    groups
}

/// Compute the `(c0, c2)` coefficients of the LSB-fold round polynomial from a flat weight vector.
///
/// The round polynomial is `p(z) = c0 + c1·z + c2·z^2` where `c1 = sum - 2·c0 - c2`. We return
/// only `c0` and `c2`; the caller derives `c1` from the running sum.
///
/// Generic over the eval type: `E = EF` uses EF · EF, `E = PF<EF>` uses `EF · F` via
/// `Algebra<F>` (5× cheaper per mul on EF5/KoalaBear) for the round-0 hot loop.
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

/// LSB-fold a base-field slice with an extension-field challenge, producing an extension-field
/// vector: `out[i] = m[2i] + r · (m[2i+1] - m[2i])` with `m ∈ F`, `r ∈ EF`, `out ∈ EF`.
fn lsb_fold_base_to_ext<EF>(m: &[PF<EF>], r: EF) -> Vec<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    fold_multilinear_lsb(m, r, &|diff, alpha| alpha * diff)
}

/// Fold an evaluation table by `l_0` LSB-fold challenges in a single pass via the eq-tensor
/// `eval_eq([ρ_{l_0-1}, .., ρ_0])`.
///
/// Equivalent to iterating `lsb_fold_base_to_ext(evals, ρ_0)` followed by `lsb_fold(.., ρ_k)` for
/// k = 1..l_0, but reads each `evals` entry exactly once. For `E = PF<EF>` the inner mul is
/// `EF · F` (via `Algebra<F>`), ~5× cheaper than the iterated fold which promotes to `EF · EF`
/// after round 0.
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

/// Finish a sumcheck round given the computed `(c0, c2)`: derive `c1`, send the polynomial over
/// Fiat-Shamir, grind, sample the challenge, update the running `sum`, and return the challenge.
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

/// Same as `lsb_sumcheck_round`, but reads the weight polynomial from a structured
/// [`SplitWeights`] representation instead of a flat vector. Computes `(c0, c2)` via
/// `SplitWeights::round_coeffs_split`, which only materializes the factored components.
#[instrument(skip_all)]
fn lsb_sumcheck_round_split<EF: ExtensionField<PF<EF>>>(
    evals: &[EF],
    split: &SplitWeights<EF>,
    sum: &mut EF,
    prover_state: &mut impl FSProver<EF>,
    pow_bits: usize,
) -> EF {
    let (c0, c2) = split.round_coeffs_split(evals);
    sumcheck_finish_round(c0, c2, sum, prover_state, pow_bits)
}

/// Base-field variant of [`lsb_sumcheck_round_split`]: `evals ∈ F^n`. Used for round 0 when the
/// committed polynomial is base-field, so the round-0 inner arithmetic stays at F × EF cost.
#[instrument(skip_all)]
fn lsb_sumcheck_round_split_base<EF: ExtensionField<PF<EF>>>(
    evals: &[PF<EF>],
    split: &SplitWeights<EF>,
    sum: &mut EF,
    prover_state: &mut impl FSProver<EF>,
    pow_bits: usize,
) -> EF {
    let (c0, c2) = split.round_coeffs_split(evals);
    sumcheck_finish_round(c0, c2, sum, prover_state, pow_bits)
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
            commitment_merkle_prover_data_b: None,
            randomness_vec: folding_randomness.0.clone(),
        })
    }

    fn folding_randomness(&self, folding_factor: usize) -> MultilinearPoint<EF> {
        MultilinearPoint(self.randomness_vec[self.randomness_vec.len() - folding_factor..].to_vec())
    }
}

/// LSB-fold a sparse selector coefficient list: `new[i] = coefs[2i] + r · (coefs[2i+1] - coefs[2i])`.
///
/// Entries at `sel = 2i` contribute `(1 - r) · coef` at `i`; entries at `sel = 2i + 1` contribute
/// `r · coef` at `i`. We aggregate per destination index so coincident-pair claims merge into a
/// single entry after folding.
fn fold_sparse_selectors<EF>(entries: &mut Vec<(usize, EF)>, r: EF)
where
    EF: ExtensionField<PF<EF>>,
{
    use std::collections::BTreeMap;
    let mut acc: BTreeMap<usize, EF> = BTreeMap::new();
    for &(sel, coef) in entries.iter() {
        let i = sel >> 1;
        let contrib = if sel & 1 == 0 { coef - r * coef } else { r * coef };
        let entry = acc.entry(i).or_insert(EF::ZERO);
        *entry += contrib;
    }
    *entries = acc.into_iter().collect();
}

/// Selector coefficients for a [`WeightGroup`].
///
/// `Sparse` carries one `(selector, coefficient)` entry per claim; it stays compact when most
/// selector slots are unused. `Dense` is reserved for groups whose selector space is densely
/// populated; it is unused in Phase 1 but exercised from Phase 2 onward.
#[derive(Debug, Clone)]
pub(crate) enum SelectCoefs<EF> {
    Sparse(Vec<(usize, EF)>),
    #[allow(dead_code)]
    Dense(Vec<EF>),
}

/// One factored term `select(x_prefix) * inner_eq(x_suffix)` of the combined weight polynomial.
///
/// Initially `inner_eq` is `eval_eq(point)` (or `matrix_next_mle_folded(point)` when is_next)
/// with length `2^m_g`. The group's weight, viewed as a function on the full `2^n` index, is
/// `weights[j] = select[j >> m_g] * inner_eq[j & (2^m_g - 1)]`. After LSB-folding, `inner_eq`
/// halves each round until it reaches size 1 ("scalar phase"), at which point the selector
/// coefficients start folding instead. The current `inner_eq.len()` implicitly encodes the
/// fold state, so the original `m_g` is not retained.
#[derive(Debug, Clone)]
pub(crate) struct WeightGroup<EF> {
    pub(crate) inner_eq: Vec<EF>,
    pub(crate) select_coefs: SelectCoefs<EF>,
}

/// Structured representation of the combined weight polynomial used in the initial sumcheck.
///
/// The weight polynomial is stored as:
///
///   weights(x) = dense_weights(x) + Σ_g select_g(x_prefix) * inner_eq_g(x_suffix)
///
/// where `dense_weights` collects the fully-dense claims (`m_g = n_total_vars`, single selector
/// `0`) and the remaining claims live as factored groups. This mirrors Plonky3 PR #1554's
/// "prefix mode" factoring, specialized to this repo's SparseStatement layout.
#[derive(Debug)]
pub(crate) struct SplitWeights<EF> {
    /// Original (unfolded) variable count. Kept for `collapse_to_flat` and for diagnostics;
    /// the per-round folded size is read from `evals.len()` or derived from component sizes.
    #[allow(dead_code)]
    pub(crate) n_total_vars: usize,
    pub(crate) groups: Vec<WeightGroup<EF>>,
    /// Flat buffer of length `2^n_total_vars` for dense claims; `None` when no dense claim has
    /// been seen yet (in that case no `2^n` allocation is paid for by the structured path).
    pub(crate) dense_weights: Option<Vec<EF>>,
}

impl<EF> SplitWeights<EF>
where
    EF: ExtensionField<PF<EF>>,
{
    /// Build the structured weight representation from a list of sparse statements plus the
    /// combination randomness `gamma`. Returns the structured weights and the accumulated
    /// `combined_sum = Σ γ^i · value_i`. The per-value indexing of `γ` matches
    /// `combine_statement_flat` exactly.
    pub(crate) fn from_statements(statements: &[SparseStatement<EF>], gamma: EF) -> (Self, EF) {
        let n = statements[0].total_num_variables;
        assert!(statements.iter().all(|e| e.total_num_variables == n));

        let mut groups: Vec<WeightGroup<EF>> = Vec::new();
        let mut dense_weights: Option<Vec<EF>> = None;
        let mut combined_sum = EF::ZERO;
        let mut gamma_pow = EF::ONE;

        for smt in statements {
            let m = smt.inner_num_variables();
            let is_dense = m == n;

            if is_dense {
                // Selector space is a single slot (selector = 0). Route into the shared dense
                // buffer so multiple dense claims share one 2^n allocation.
                let dw = dense_weights.get_or_insert_with(|| EF::zero_vec(1 << n));
                if smt.is_next {
                    // No in-place accumulator exists for matrix_next_mle_folded; materialize
                    // once per statement and fan out across values.
                    let inner_poly = matrix_next_mle_folded(&smt.point.0);
                    for v in &smt.values {
                        assert_eq!(v.selector, 0, "dense SparseStatement with non-zero selector");
                        dw.par_iter_mut().zip(inner_poly.par_iter()).for_each(|(d, &p)| {
                            *d += p * gamma_pow;
                        });
                        combined_sum += v.value * gamma_pow;
                        gamma_pow *= gamma;
                    }
                } else {
                    for v in &smt.values {
                        assert_eq!(v.selector, 0, "dense SparseStatement with non-zero selector");
                        // `compute_sparse_eval_eq` writes `gamma_pow · eq(point, ·)` directly
                        // into `dw` in-place (INITIALIZED=true add mode), avoiding a fresh
                        // `2^n` buffer per dense statement — critical when OOD samples make
                        // several dense claims in sequence.
                        compute_sparse_eval_eq::<EF>(v.selector, &smt.point.0, dw, gamma_pow);
                        combined_sum += v.value * gamma_pow;
                        gamma_pow *= gamma;
                    }
                }
            } else {
                // Factored group: one inner_eq, one coefficient per claim's selector.
                let inner_eq: Vec<EF> = if smt.is_next {
                    matrix_next_mle_folded(&smt.point.0)
                } else {
                    eval_eq(&smt.point.0)
                };

                // Reject duplicate selectors within a single statement, matching the flat path.
                let mut seen: Vec<usize> = smt.values.iter().map(|v| v.selector).collect();
                seen.sort_unstable();
                assert!(
                    seen.windows(2).all(|w| w[0] != w[1]),
                    "Duplicate selectors in sparse statement"
                );

                let mut coefs = Vec::with_capacity(smt.values.len());
                for v in &smt.values {
                    coefs.push((v.selector, gamma_pow));
                    combined_sum += v.value * gamma_pow;
                    gamma_pow *= gamma;
                }

                groups.push(WeightGroup {
                    inner_eq,
                    select_coefs: SelectCoefs::Sparse(coefs),
                });
            }
        }

        (
            Self {
                n_total_vars: n,
                groups,
                dense_weights,
            },
            combined_sum,
        )
    }

    /// Compute the `(c0, c2)` coefficients of the LSB-fold round polynomial directly from the
    /// structured representation, without materializing a `2^(n-round)` weight vector.
    ///
    /// Generic over the eval type: `E = EF` for subsequent rounds, `E = PF<EF>` for round 0
    /// when the committed polynomial is base-field (uses `EF · F` via `Algebra<F>`, ~5× cheaper
    /// per mul on EF5/KoalaBear).
    pub(crate) fn round_coeffs_split<E>(&self, evals: &[E]) -> (EF, EF)
    where
        EF: Mul<E, Output = EF>,
        E: Copy + Send + Sync + Sub<E, Output = E>,
    {
        let n_remaining = evals.len();
        assert!(n_remaining >= 2 && n_remaining.is_power_of_two());
        let half = n_remaining / 2;

        let mut c0 = EF::ZERO;
        let mut c2 = EF::ZERO;

        // Dense weights contribution.
        if let Some(dw) = &self.dense_weights {
            assert_eq!(dw.len(), n_remaining);
            let (d0, d2) = round_coeffs_flat(evals, dw);
            c0 += d0;
            c2 += d2;
        }

        for group in &self.groups {
            let eq_len = group.inner_eq.len();
            if eq_len >= 2 {
                // Inner phase: weight[j] = select[a] * inner_eq[b], where j = a * eq_len + b.
                let selector_len = n_remaining / eq_len; // 2^(selector_bits_remaining)
                match &group.select_coefs {
                    SelectCoefs::Sparse(entries) => {
                        for &(a, coef) in entries {
                            assert!(a < selector_len);
                            let base = a * eq_len;
                            let (g0, g2) = round_coeffs_flat(&evals[base..base + eq_len], &group.inner_eq);
                            c0 += g0 * coef;
                            c2 += g2 * coef;
                        }
                    }
                    SelectCoefs::Dense(coefs) => {
                        assert_eq!(coefs.len(), selector_len);
                        let (g0, g2) = coefs
                            .par_iter()
                            .enumerate()
                            .map(|(a, &coef)| {
                                let base = a * eq_len;
                                let (g0, g2) = round_coeffs_flat(&evals[base..base + eq_len], &group.inner_eq);
                                (g0 * coef, g2 * coef)
                            })
                            .reduce(|| (EF::ZERO, EF::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2));
                        c0 += g0;
                        c2 += g2;
                    }
                }
            } else {
                // Scalar phase: weight[j] = scalar * select_folded[j], with select_folded over
                // `n_remaining` entries.
                let scalar = group.inner_eq[0];
                match &group.select_coefs {
                    SelectCoefs::Sparse(entries) => {
                        for &(sel, coef) in entries {
                            assert!(sel < n_remaining);
                            let i = sel >> 1;
                            let effective = scalar * coef;
                            let diff_e = evals[2 * i + 1] - evals[2 * i];
                            if sel & 1 == 0 {
                                // lo_w = effective, hi_w = 0 at this (i).
                                c0 += effective * evals[2 * i];
                                c2 -= effective * diff_e;
                            } else {
                                // lo_w = 0, hi_w = effective at this (i).
                                c2 += effective * diff_e;
                            }
                        }
                    }
                    SelectCoefs::Dense(coefs) => {
                        assert_eq!(coefs.len(), n_remaining);
                        let (g0, g2) = (0..half)
                            .into_par_iter()
                            .map(|i| {
                                let lo_e = evals[2 * i];
                                let hi_e = evals[2 * i + 1];
                                let lo_w = coefs[2 * i] * scalar;
                                let hi_w = coefs[2 * i + 1] * scalar;
                                (lo_w * lo_e, (hi_w - lo_w) * (hi_e - lo_e))
                            })
                            .reduce(|| (EF::ZERO, EF::ZERO), |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2));
                        c0 += g0;
                        c2 += g2;
                    }
                }
            }
        }

        (c0, c2)
    }

    /// Apply one LSB-fold round with challenge `r` to every component of the structured weights.
    ///
    /// Groups in the inner phase (`inner_eq.len() > 1`) fold their `inner_eq`; groups in the
    /// scalar phase (`inner_eq.len() == 1`) fold their `select_coefs`. The dense buffer folds as
    /// a plain vector.
    pub(crate) fn fold(&mut self, r: EF) {
        if let Some(dw) = &mut self.dense_weights {
            let half = dw.len() / 2;
            let folded: Vec<EF> = (0..half)
                .into_par_iter()
                .map(|i| dw[2 * i] + r * (dw[2 * i + 1] - dw[2 * i]))
                .collect();
            *dw = folded;
        }

        for group in &mut self.groups {
            if group.inner_eq.len() >= 2 {
                // Inner phase: LSB-fold the inner equality table.
                let half = group.inner_eq.len() / 2;
                let folded: Vec<EF> = (0..half)
                    .into_par_iter()
                    .map(|i| group.inner_eq[2 * i] + r * (group.inner_eq[2 * i + 1] - group.inner_eq[2 * i]))
                    .collect();
                group.inner_eq = folded;
            } else {
                // Scalar phase: LSB-fold the selector coefficients.
                match &mut group.select_coefs {
                    SelectCoefs::Sparse(entries) => {
                        fold_sparse_selectors(entries, r);
                    }
                    SelectCoefs::Dense(coefs) => {
                        let half = coefs.len() / 2;
                        let folded: Vec<EF> = (0..half)
                            .into_par_iter()
                            .map(|i| coefs[2 * i] + r * (coefs[2 * i + 1] - coefs[2 * i]))
                            .collect();
                        *coefs = folded;
                    }
                }
            }
        }
    }

    /// Materialize the structured weights as a flat `Vec<EF>` of length `target_size`.
    ///
    /// `target_size` must equal the current weight polynomial size (i.e. `2^(n_total_vars - k)`
    /// where `k` is the number of fold rounds applied). In particular:
    ///   - Immediately after `from_statements`, `target_size == 2^n_total_vars`.
    ///   - After `k` calls to `fold`, `target_size == 2^(n_total_vars - k)`.
    ///
    /// This consumes `self` so the `dense_weights` buffer (when present) can be reused in-place
    /// without copying.
    pub(crate) fn into_flat(self, target_size: usize) -> Vec<EF> {
        let mut out = self.dense_weights.unwrap_or_else(|| EF::zero_vec(target_size));
        assert_eq!(out.len(), target_size, "into_flat: dense buffer size mismatch");

        for group in &self.groups {
            let eq_len = group.inner_eq.len();
            let sel_len = target_size / eq_len;
            assert_eq!(eq_len * sel_len, target_size, "into_flat: group size mismatch");
            match &group.select_coefs {
                SelectCoefs::Sparse(entries) => {
                    // Sort by selector so non-overlapping slices can be split and written in
                    // parallel without aliasing.
                    let mut sorted = entries.clone();
                    sorted.sort_unstable_by_key(|(sel, _)| *sel);
                    let split_points: Vec<usize> = sorted.iter().map(|(sel, _)| *sel * eq_len).collect();
                    let mut chunks = split_at_mut_many(&mut out, &split_points);
                    chunks.remove(0); // discard the prefix before the first selector
                    chunks
                        .into_par_iter()
                        .zip(sorted.par_iter())
                        .for_each(|(chunk, &(sel, coef))| {
                            assert!(sel < sel_len);
                            chunk[..eq_len]
                                .par_iter_mut()
                                .zip(group.inner_eq.par_iter())
                                .for_each(|(o, &i)| *o += i * coef);
                        });
                }
                SelectCoefs::Dense(coefs) => {
                    assert_eq!(coefs.len(), sel_len);
                    for (sel, &coef) in coefs.iter().enumerate() {
                        out[sel * eq_len..(sel + 1) * eq_len]
                            .par_iter_mut()
                            .zip(group.inner_eq.par_iter())
                            .for_each(|(o, &i)| *o += i * coef);
                    }
                }
            }
        }

        out
    }
}
