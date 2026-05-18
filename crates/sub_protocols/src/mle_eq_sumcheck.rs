use std::fmt::Debug;

use backend::*;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::OuterSumcheckSession;

/// Sumcheck session for an identity of the form
///   sum = Σ_x eq(p, x) · P(x)
/// where `P` is a single multilinear polynomial and `p` is a fixed point.
///
/// The session folds variables `X_{L-1}, X_{L-2}, ..., X_0` (right-to-left), matching
/// the convention used by [`AirSumcheckSession`] so it can be batched alongside
/// AIR sessions inside [`prove_batched_air_sumcheck`].
///
/// `eq_factor[k]` is the eq-point coordinate for `X_k`, and the last element is
/// popped each round (the one consumed by the current challenge).
#[derive(Debug)]
pub struct MleEqSumcheckSession<'a, EF: ExtensionField<PF<EF>>> {
    poly: MleGroup<'a, EF>,
    eq_factor: Vec<EF>,
    sum: EF,
    missing_mul_factor: EF,
    initial_n_vars: usize,
    rounds_done: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>> MleEqSumcheckSession<'a, EF> {
    /// `poly` must contain exactly one column. `eq_factor` has the same number of
    /// entries as `poly` has variables, with `eq_factor[k]` matching variable `X_k`.
    pub fn new(poly: MleGroup<'a, EF>, eq_factor: Vec<EF>, sum: EF) -> Self {
        let initial_n_vars = poly.by_ref().n_vars();
        assert_eq!(poly.by_ref().group_size(), 1, "MleEqSumcheckSession expects a single polynomial");
        assert_eq!(eq_factor.len(), initial_n_vars);
        Self {
            poly,
            eq_factor,
            sum,
            missing_mul_factor: EF::ONE,
            initial_n_vars,
            rounds_done: 0,
        }
    }
}

impl<'a, EF: ExtensionField<PF<EF>>> OuterSumcheckSession<EF> for MleEqSumcheckSession<'a, EF> {
    fn initial_n_vars(&self) -> usize {
        self.initial_n_vars
    }

    fn sum(&self) -> EF {
        self.sum
    }

    fn bare_degree(&self) -> usize {
        // P is multilinear; without the eq linear factor on the current variable,
        // the bare round polynomial is degree-1 in the folded variable.
        1
    }

    fn eq_alpha(&self) -> EF {
        *self.eq_factor.last().unwrap()
    }

    fn compute_bare_round_poly(&mut self) -> DensePolynomial<EF> {
        let n_remaining = self.initial_n_vars - self.rounds_done;
        // The current variable being folded is X_{L-r-1} (the LSB of the
        // storage index, since X_0 sits at the MSB in the canonical layout).
        // Partial eq runs over X_0 .. X_{L-r-2}.
        let partial_alphas = &self.eq_factor[..n_remaining - 1];
        let eq_vec = eval_eq(partial_alphas);

        let bare_0 = compute_bare_at_zero(&self.poly.by_ref(), &eq_vec);
        let bare_0_scaled = bare_0 * self.missing_mul_factor;

        let alpha = self.eq_alpha();
        let bare_1_scaled = (self.sum - (EF::ONE - alpha) * bare_0_scaled) / alpha;

        DensePolynomial::lagrange_interpolation(&[
            (PF::<EF>::ZERO, bare_0_scaled),
            (PF::<EF>::ONE, bare_1_scaled),
        ])
        .unwrap()
    }

    fn process_challenge(&mut self, challenge: EF, bare_poly: &DensePolynomial<EF>) {
        let alpha = self.eq_alpha();
        let eq_eval = (EF::ONE - alpha) * (EF::ONE - challenge) + alpha * challenge;
        self.sum = bare_poly.evaluate(challenge) * eq_eval;
        self.missing_mul_factor *= eq_eval;

        // Fold the LSB, which corresponds to X_{L-r-1}.
        self.poly = self.poly.by_ref().fold_at_bit(challenge, 0).into();

        self.eq_factor.pop();
        self.rounds_done += 1;
    }

    fn final_column_evals(&self) -> Vec<EF> {
        column_evals_single(&self.poly.by_ref())
    }
}

/// Σ_j eq_vec[j] · P[2j]. The "even index" half corresponds to fixing the LSB
/// (currently folded variable) to 0.
fn compute_bare_at_zero<EF: ExtensionField<PF<EF>>>(poly: &MleGroupRef<'_, EF>, eq_vec: &[EF]) -> EF {
    match poly {
        MleGroupRef::Base(cols) => {
            assert_eq!(cols.len(), 1);
            let c = cols[0];
            debug_assert_eq!(c.len(), eq_vec.len() * 2);
            (0..eq_vec.len()).into_par_iter().map(|j| eq_vec[j] * c[2 * j]).sum()
        }
        MleGroupRef::Extension(cols) => {
            assert_eq!(cols.len(), 1);
            let c = cols[0];
            debug_assert_eq!(c.len(), eq_vec.len() * 2);
            (0..eq_vec.len()).into_par_iter().map(|j| eq_vec[j] * c[2 * j]).sum()
        }
        MleGroupRef::BasePacked(_) | MleGroupRef::ExtensionPacked(_) => {
            // After the first fold the polynomial is unpacked Extension; the only way to
            // hit a packed variant is at round 0 with packed base input. The caller wires
            // memory/memory_acc/bytecode_acc as unpacked base, so this branch is unused.
            unimplemented!("MleEqSumcheckSession does not support packed inputs");
        }
    }
}

fn column_evals_single<EF: ExtensionField<PF<EF>>>(poly: &MleGroupRef<'_, EF>) -> Vec<EF> {
    match poly {
        MleGroupRef::Base(cols) => {
            assert_eq!(cols.len(), 1);
            assert_eq!(cols[0].len(), 1);
            vec![EF::from(cols[0][0])]
        }
        MleGroupRef::Extension(cols) => {
            assert_eq!(cols.len(), 1);
            assert_eq!(cols[0].len(), 1);
            vec![cols[0][0]]
        }
        _ => unimplemented!("MleEqSumcheckSession does not support packed outputs"),
    }
}
