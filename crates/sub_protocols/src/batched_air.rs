use std::collections::BTreeMap;
use std::fmt::Debug;

use backend::*;
use lean_vm::ColIndex;

pub trait OuterSumcheckSession<EF: ExtensionField<PF<EF>>>: Debug {
    fn n_vars(&self) -> usize;
    fn sum(&self) -> EF;
    fn bare_degree(&self) -> usize;
    fn eq_alpha(&self) -> Option<EF>;
    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF>;
    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>);
    fn finalize_inner_sums(&self) -> Vec<EF>;
}

#[derive(Debug)]
pub struct SumcheckSessionState<'a, EF: ExtensionField<PF<EF>>, A: Air>
where
    A::ExtraData: AlphaPowers<EF>,
{
    multilinears: MleGroup<'a, EF>,
    eq_factor_and_split: Option<(Vec<EF>, SplitEq<EF>)>,
    sum: EF,
    missing_mul_factors: Option<EF>,
    computation: A,
    extra_data: A::ExtraData,
}

impl<'a, EF: ExtensionField<PF<EF>>, A: Air> SumcheckSessionState<'a, EF, A>
where
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF>,
{
    pub fn new(
        packed_multilinears: MleGroup<'a, EF>,
        eq_factor: Option<Vec<EF>>,
        sum: EF,
        computation: A,
        extra_data: A::ExtraData,
    ) -> Self {
        let n_vars = packed_multilinears.n_vars();
        let eq_factor_and_split = eq_factor.map(|eq_point| {
            assert_eq!(eq_point.len(), n_vars);
            let split_eq = SplitEq::new(&eq_point[1..]);
            (eq_point, split_eq)
        });
        Self {
            multilinears: packed_multilinears,
            eq_factor_and_split,
            sum,
            missing_mul_factors: None,
            computation,
            extra_data,
        }
    }
}

impl<'a, EF, A> OuterSumcheckSession<EF> for SumcheckSessionState<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + Debug + 'static,
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF> + Debug,
{
    fn n_vars(&self) -> usize {
        self.multilinears.n_vars()
    }

    fn sum(&self) -> EF {
        self.sum
    }

    fn bare_degree(&self) -> usize {
        self.computation.degree()
    }

    fn eq_alpha(&self) -> Option<EF> {
        self.eq_factor_and_split.as_ref().map(|(eq, _)| eq[0])
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        // Unpack SIMD when too few variables remain
        if self.multilinears.is_packed() && self.multilinears.n_vars() <= 1 + packing_log_width::<EF>() {
            let old = std::mem::replace(
                &mut self.multilinears,
                MleGroup::Owned(MleGroupOwned::Extension(vec![])),
            );
            self.multilinears = MleGroup::Owned(old.by_ref().unpack().as_owned_or_clone());
        }

        let computation_degree = self.computation.degree();
        let sc_params = SumcheckComputeParams {
            split_eq: self.eq_factor_and_split.as_ref().map(|(_, se)| se),
            first_eq_factor: self.eq_factor_and_split.as_ref().map(|(eq, _)| eq[0]),
            computation: &self.computation,
            extra_data: &self.extra_data,
            missing_mul_factor: self.missing_mul_factors,
            sum: self.sum,
        };

        let p_evals = sumcheck_compute(&self.multilinears.by_ref(), sc_params, computation_degree);

        // Reconstruct h(1) from the claimed-sum constraint:
        //   with eq:    (1−α)·h(0) + α·h(1) = sum   →  h(1) = (sum − (1−α)·h(0)) / α
        //   without eq: h(0) + h(1) = sum             →  h(1) = sum − h(0)
        let h_at_1 = if let Some((eq, _)) = &self.eq_factor_and_split {
            (self.sum - (EF::ONE - eq[0]) * p_evals[0]) / eq[0]
        } else {
            self.sum - p_evals[0]
        };

        // p_evals = [h(0), h(2), h(3), …, h(degree)]   (h(1) was omitted)
        let mut full_evals = Vec::with_capacity(computation_degree + 2);
        full_evals.push(p_evals[0]); // h(0)
        full_evals.push(h_at_1); // h(1)
        full_evals.extend_from_slice(&p_evals[1..]); // h(2) … h(degree)

        DensePolynomial::lagrange_interpolation(
            &full_evals
                .iter()
                .enumerate()
                .map(|(i, &v)| (PF::<EF>::from_usize(i), v))
                .collect::<Vec<_>>(),
        )
        .unwrap()
    }

    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>) {
        // New running sum = h(challenge)
        self.sum = bare_poly.evaluate(challenge);

        // Multiply by eq_linear(α, challenge) and advance eq state
        if let Some((eq_factor, split_eq)) = &mut self.eq_factor_and_split {
            let eq_eval = (EF::ONE - eq_factor[0]) * (EF::ONE - challenge) + eq_factor[0] * challenge;
            self.sum *= eq_eval;

            self.missing_mul_factors = Some(
                eq_eval * self.missing_mul_factors.unwrap_or(EF::ONE)
                    / (EF::ONE - eq_factor.get(1).copied().unwrap_or_default()),
            );
            eq_factor.remove(0);
            split_eq.truncate_half();
        }

        // Fold multilinears eagerly (store_intermediate_foldings = true)
        let folded = self.multilinears.by_ref().fold(challenge);
        self.multilinears = MleGroup::Owned(folded);
    }

    fn finalize_inner_sums(&self) -> Vec<EF> {
        self.multilinears
            .by_ref()
            .as_extension()
            .unwrap()
            .iter()
            .map(|m| {
                assert_eq!(m.len(), 1);
                m[0]
            })
            .collect()
    }
}

#[derive(Debug)]
pub struct BatchedProverEntry<'a, EF: ExtensionField<PF<EF>>> {
    pub session: Box<dyn OuterSumcheckSession<EF> + 'a>,
    pub eta_power: EF,
    /// Initial number of variables for this table.
    pub table_n_vars: usize,
}

pub fn prove_batched_outer_sumcheck<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    entries: &mut [BatchedProverEntry<'a, EF>],
) -> MultilinearPoint<EF> {
    let n_rounds = entries.iter().map(|e| e.table_n_vars).max().unwrap_or(0);
    let max_full_degree = entries.iter().map(|e| e.session.bare_degree() + 1).max().unwrap_or(1);

    let mut challenges = Vec::with_capacity(n_rounds);

    // Per-table prefix multiplier K_t.  Grows each round during padding,
    // freezes once the table enters its active phase.
    let mut k: Vec<EF> = vec![EF::ONE; entries.len()];

    let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
    let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; entries.len()];

    for round in 0..n_rounds {
        combined_coeffs.fill(EF::ZERO);
        bare_polys.fill(None);

        for (idx, entry) in entries.iter_mut().enumerate() {
            let join_round = n_rounds - entry.table_n_vars;
            if round < join_round {
                // Padding: contribute the line K_t · S_t · Y
                combined_coeffs[1] += entry.eta_power * k[idx] * entry.session.sum();
            } else {
                // Active: compute bare poly, expand by eq_linear, scale by frozen K_t
                let bare_poly = entry.session.compute_bare_round_poly();
                let full_coeffs = match entry.session.eq_alpha() {
                    Some(alpha) => expand_bare_to_full(&bare_poly.coeffs, alpha),
                    None => bare_poly.coeffs.clone(),
                };
                for (i, &c) in full_coeffs.iter().enumerate() {
                    combined_coeffs[i] += entry.eta_power * k[idx] * c;
                }
                bare_polys[idx] = Some(bare_poly);
            }
        }

        prover_state.add_sumcheck_polynomial(&combined_coeffs, None);
        let challenge = prover_state.sample();
        challenges.push(challenge);

        for (idx, entry) in entries.iter_mut().enumerate() {
            let join_round = n_rounds - entry.table_n_vars;
            if round < join_round {
                // Still padding: K_t grows
                k[idx] *= challenge;
            } else if let Some(bare_poly) = &bare_polys[idx] {
                // Active: process the challenge in the table's sumcheck (K_t stays frozen)
                entry.session.process_challenge(challenge, bare_poly);
            }
        }
    }

    MultilinearPoint(challenges)
}

pub fn compute_shifted_columns<F: Field>(air_down_column_indexes: &[usize], columns: &[&[F]]) -> Vec<Vec<F>> {
    air_down_column_indexes
        .par_iter()
        .map(|&col_index| column_shifted(columns[col_index]))
        .collect()
}

fn column_shifted<F: Field>(column: &[F]) -> Vec<F> {
    let mut down = unsafe { uninitialized_vec(column.len()) };
    parallel_clone(&column[1..], &mut down[..column.len() - 1]);
    down[column.len() - 1] = column[column.len() - 1];
    down
}

pub fn split_air_inner_evals<EF: ExtensionField<PF<EF>>, A: Air>(
    air: &A,
    inner_evals: &[EF],
    all_challenges: &[EF],
    table_n_vars: usize,
) -> (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>) {
    let n_up = air.n_columns();
    debug_assert_eq!(inner_evals.len(), n_up + air.n_down_columns());

    let suffix_start = all_challenges.len() - table_n_vars;
    let point = MultilinearPoint(all_challenges[suffix_start..].to_vec());

    let evals_eq: BTreeMap<ColIndex, EF> = inner_evals[..n_up].iter().copied().enumerate().collect();
    let evals_next: BTreeMap<ColIndex, EF> = inner_evals[n_up..]
        .iter()
        .zip(air.down_column_indexes())
        .map(|(&v, col_index)| (col_index, v))
        .collect();

    (point, evals_eq, evals_next)
}

pub fn back_loaded_table_contribution<EF: ExtensionField<PF<EF>>>(
    bus_point: &[EF],
    all_challenges: &[EF],
    constraint_eval: EF,
    eta_power: EF,
) -> EF {
    let n_t = bus_point.len();
    let n_max = all_challenges.len();
    let suffix_start = n_max - n_t;
    let challenge_suffix = &all_challenges[suffix_start..];
    let eq_val = MultilinearPoint(bus_point.to_vec()).eq_poly_outside(&MultilinearPoint(challenge_suffix.to_vec()));
    let k_t: EF = all_challenges[..suffix_start].iter().copied().product();
    eta_power * k_t * eq_val * constraint_eval
}
