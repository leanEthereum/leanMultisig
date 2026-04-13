use std::collections::BTreeMap;
use std::fmt::Debug;

use backend::*;
use lean_vm::ColIndex;

// back-loaded batched sumcheck (see https://hackmd.io/s/HyxaupAAA)

pub trait OuterSumcheckSession<EF: ExtensionField<PF<EF>>>: Debug {
    fn initial_n_vars(&self) -> usize;
    fn sum(&self) -> EF;
    fn bare_degree(&self) -> usize;
    fn eq_alpha(&self) -> EF;
    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF>;
    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>);
    fn final_column_evals(&self) -> Vec<EF>;
}

#[derive(Debug)]
pub struct AirSumcheckSession<'a, EF: ExtensionField<PF<EF>>, A: Air>
where
    A::ExtraData: AlphaPowers<EF>,
{
    multilinears: MleGroup<'a, EF>,
    eq_factor_and_split: Option<(Vec<EF>, SplitEq<EF>)>,
    sum: EF,
    missing_mul_factors: Option<EF>,
    computation: A,
    extra_data: A::ExtraData,
    initial_n_vars: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>, A: Air> AirSumcheckSession<'a, EF, A>
where
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF>,
{
    pub fn new(
        packed_multilinears: MleGroup<'a, EF>,
        eq_factor: Vec<EF>,
        sum: EF,
        computation: A,
        extra_data: A::ExtraData,
    ) -> Self {
        let initial_n_vars = packed_multilinears.n_vars();
        assert_eq!(eq_factor.len(), initial_n_vars);
        let split_eq = SplitEq::new(&eq_factor[1..]);
        Self {
            multilinears: packed_multilinears,
            eq_factor_and_split: Some((eq_factor, split_eq)),
            sum,
            missing_mul_factors: None,
            computation,
            extra_data,
            initial_n_vars,
        }
    }
}

impl<'a, EF, A> OuterSumcheckSession<EF> for AirSumcheckSession<'a, EF, A>
where
    EF: ExtensionField<PF<EF>>,
    A: Air + Debug + 'static,
    A::ExtraData: AlphaPowers<EF> + AlphaPowersMut<EF> + Debug,
{
    fn initial_n_vars(&self) -> usize {
        self.initial_n_vars
    }

    fn sum(&self) -> EF {
        self.sum
    }

    fn bare_degree(&self) -> usize {
        self.computation.degree()
    }

    fn eq_alpha(&self) -> EF {
        self.eq_factor_and_split.as_ref().unwrap().0[0]
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        if self.multilinears.is_packed() && self.multilinears.n_vars() <= 1 + packing_log_width::<EF>() {
            let old = std::mem::replace(
                &mut self.multilinears,
                MleGroup::Owned(MleGroupOwned::Extension(vec![])),
            );
            self.multilinears = MleGroup::Owned(old.by_ref().unpack().as_owned_or_clone());
        }
        compute_round_polynomial(
            &mut self.multilinears,
            None,
            &self.computation,
            &self.eq_factor_and_split,
            &self.extra_data,
            self.sum,
            self.missing_mul_factors,
        )
    }

    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>) {
        let mut n_vars = self.multilinears.n_vars();
        on_challenge_received(
            &mut self.multilinears,
            &mut n_vars,
            &mut self.eq_factor_and_split,
            &mut self.sum,
            &mut self.missing_mul_factors,
            challenge,
            bare_poly,
            true,
        );
    }

    fn final_column_evals(&self) -> Vec<EF> {
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

pub fn prove_batched_air_sumcheck<'a, EF: ExtensionField<PF<EF>>>(
    prover_state: &mut impl FSProver<EF>,
    sessions: &mut [Box<dyn OuterSumcheckSession<EF> + 'a>],
    eta: EF,
) -> MultilinearPoint<EF> {
    let n_rounds = sessions.iter().map(|s| s.initial_n_vars()).max().unwrap_or(0);
    let max_full_degree = sessions.iter().map(|s| s.bare_degree() + 1).max().unwrap_or(1);
    let eta_powers: Vec<EF> = eta.powers().collect_n(sessions.len());

    let mut challenges = Vec::with_capacity(n_rounds);
    // Per-table prefix multiplier K_t.  Grows each round during padding,
    // freezes once the table enters its active phase.
    let mut k: Vec<EF> = vec![EF::ONE; sessions.len()];
    let mut combined_coeffs = EF::zero_vec(max_full_degree + 1);
    let mut bare_polys: Vec<Option<DensePolynomial<EF>>> = vec![None; sessions.len()];

    for round in 0..n_rounds {
        combined_coeffs.fill(EF::ZERO);
        bare_polys.fill(None);

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                // Padding
                combined_coeffs[1] += eta_powers[idx] * k[idx] * session.sum();
            } else {
                // Active: compute bare poly, expand by eq_linear, scale by frozen K_t
                let bare_poly = session.compute_bare_round_poly();
                let full_coeffs = expand_bare_to_full(&bare_poly.coeffs, session.eq_alpha());
                for (i, &c) in full_coeffs.iter().enumerate() {
                    combined_coeffs[i] += eta_powers[idx] * k[idx] * c;
                }
                bare_polys[idx] = Some(bare_poly);
            }
        }

        prover_state.add_sumcheck_polynomial(&combined_coeffs, None);
        let challenge = prover_state.sample();
        challenges.push(challenge);

        for (idx, session) in sessions.iter_mut().enumerate() {
            let join_round = n_rounds - session.initial_n_vars();
            if round < join_round {
                k[idx] *= challenge;
            } else if let Some(bare_poly) = &bare_polys[idx] {
                session.process_challenge(challenge, bare_poly);
            }
        }
    }

    MultilinearPoint(challenges)
}

pub fn compute_shifted_columns<F: Field>(air_down_column_indexes: &[usize], columns: &[&[F]]) -> Vec<Vec<F>> {
    air_down_column_indexes
        .par_iter()
        .map(|&col_index| {
            let column = columns[col_index];
            let mut down = unsafe { uninitialized_vec(column.len()) };
            parallel_clone(&column[1..], &mut down[..column.len() - 1]);
            down[column.len() - 1] = column[column.len() - 1];
            down
        })
        .collect()
}

pub fn columns_evals_up_and_down<EF: ExtensionField<PF<EF>>, A: Air>(
    air: &A,
    col_evals: &[EF],
    sumcheck_air_point: &[EF],
    table_n_vars: usize,
) -> (MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>) {
    let n_up = air.n_columns();
    debug_assert_eq!(col_evals.len(), n_up + air.n_down_columns());

    let suffix_start = sumcheck_air_point.len() - table_n_vars;
    let point = MultilinearPoint(sumcheck_air_point[suffix_start..].to_vec());

    let evals_eq: BTreeMap<ColIndex, EF> = col_evals[..n_up].iter().copied().enumerate().collect();
    let evals_next: BTreeMap<ColIndex, EF> = col_evals[n_up..]
        .iter()
        .zip(air.down_column_indexes())
        .map(|(&v, col_index)| (col_index, v))
        .collect();

    (point, evals_eq, evals_next)
}

pub fn back_loaded_table_contribution<EF: ExtensionField<PF<EF>>>(
    bus_point: &[EF],
    sumcheck_air_point: &[EF],
    constraint_eval: EF,
    eta_power: EF,
) -> EF {
    let n_t = bus_point.len();
    let n_max = sumcheck_air_point.len();
    let suffix_start = n_max - n_t;
    let suffix = &sumcheck_air_point[suffix_start..];
    let eq_val = MultilinearPoint(bus_point.to_vec()).eq_poly_outside(&MultilinearPoint(suffix.to_vec()));
    let k_t: EF = sumcheck_air_point[..suffix_start].iter().copied().product();
    eta_power * k_t * eq_val * constraint_eval
}
