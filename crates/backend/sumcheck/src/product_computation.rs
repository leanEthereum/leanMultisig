use std::ops::Sub;

use fiat_shamir::*;
use field::*;
use poly::*;
use rayon::prelude::*;
use tracing::instrument;

use crate::{SumcheckComputation, sumcheck_prove_many_rounds};

#[derive(Debug)]
pub struct ProductComputation;

impl<EF: ExtensionField<PF<EF>>> SumcheckComputation<EF> for ProductComputation {
    type ExtraData = Vec<EF>;

    fn degree(&self) -> usize {
        2
    }
    #[inline(always)]
    fn eval_base(&self, _point: &[PF<EF>], _: &Self::ExtraData) -> EF {
        unreachable!()
    }
    #[inline(always)]
    fn eval_extension(&self, point: &[EF], _: &Self::ExtraData) -> EF {
        point[0] * point[1]
    }
    #[inline(always)]
    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        EFPacking::<EF>::from(point[0] * point[1])
    }
    #[inline(always)]
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &Self::ExtraData) -> EFPacking<EF> {
        point[0] * point[1]
    }
}

// ---------------------------------------------------------------------------
// SVO (Small Value Optimization) constants
// ---------------------------------------------------------------------------

/// Number of SVO rounds (variables handled by the precomputed-accumulator phase).
const ELL_0: usize = 2;
/// Number of slabs = 2^ELL_0.
const N_BLOCK_FACTOR: usize = 1 << ELL_0; // 4
/// Total number of accumulators: 2 (round 1) + 6 (round 2).
const N_ACCUM: usize = 2 + 6; // 8

// ---------------------------------------------------------------------------
// Ternary extension
// ---------------------------------------------------------------------------

/// Extend 4 binary evaluations to all 9 ternary evaluations.
///
/// Ternary encoding: digit 0 = ∞ (leading coeff / finite difference),
/// digit 1 = binary 0, digit 2 = binary 1.
/// `nat3(β1, β2) = β1 + 3·β2`.
///
/// Slab k is at memory position k·n_block and holds evaluations at:
///   (x1 = k&1, x2 = (k>>1)&1)
/// where x2 = MSB (round-1 variable), x1 = LSB (round-2 variable).
/// Binary positions in nat3 space: {4, 5, 7, 8}.
///
/// 5 subtractions total: 2 (β1-direction) + 3 (β2).
#[inline(always)]
fn extend_ternary_2<T: Copy + Sub<Output = T>>(binary: [T; 4]) -> [T; 9] {
    let mut t = [binary[0]; 9]; // placeholder; every position is overwritten before use

    // Place binary values at their nat3 positions
    t[4] = binary[0]; // (β1=1,β2=1): slab 0 (x1=0,x2=0)
    t[5] = binary[1]; // (β1=2,β2=1): slab 1 (x1=1,x2=0)
    t[7] = binary[2]; // (β1=1,β2=2): slab 2 (x1=0,x2=1)
    t[8] = binary[3]; // (β1=2,β2=2): slab 3 (x1=1,x2=1)

    // Extend β1 (x1 direction): ∞ = difference between x1=1 and x1=0
    t[3] = t[5] - t[4]; // nat3(0,1)=3
    t[6] = t[8] - t[7]; // nat3(0,2)=6

    // Extend β2 (x2 direction): ∞ = difference between x2=1 and x2=0
    t[0] = t[6] - t[3]; // nat3(0,0)=0
    t[1] = t[7] - t[4]; // nat3(1,0)=1
    t[2] = t[8] - t[5]; // nat3(2,0)=2

    t
}

// ---------------------------------------------------------------------------
// SVO Phase 1: Accumulate ternary products
// ---------------------------------------------------------------------------

/// Accumulate one block's contribution into the 8 SVO accumulators.
///
/// Accumulator layout (MSB-first binding: round 1 = x2 = β2):
/// - acc[β2]                (β2∈{0,1}, round-1 poles)
/// - acc[2 + β2*2 + β1]    (β2∈{0,1,2}, β1∈{0,1}, round-2 poles)
///
/// Dispatch:
/// - Round 1: β2≤1 && β1≥1  → acc[β2]
/// - Round 2: β1≤1           → acc[2 + β2*2 + β1]
#[inline(always)]
fn process_svo_block<EF: ExtensionField<PF<EF>>>(
    i: usize,
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    n_block: usize,
    acc: &mut [EFPacking<EF>; N_ACCUM],
) {
    // Load 4 slab values for position i
    let a: [PFPacking<EF>; 4] = std::array::from_fn(|k| evals[k * n_block + i]);
    let b: [EFPacking<EF>; 4] = std::array::from_fn(|k| weights[k * n_block + i]);

    let at = extend_ternary_2(a);
    let bt = extend_ternary_2(b);

    // 8 sl products (nat3=8 ≡ β=(2,2) contributes to no round — skipped).
    let p0 = bt[0] * at[0]; // β=(0,0) → r2 acc[2]
    let p1 = bt[1] * at[1]; // β=(1,0) → r2 acc[3], r1 acc[0]
    let p2 = bt[2] * at[2]; // β=(2,0) → r1 acc[0]
    let p3 = bt[3] * at[3]; // β=(0,1) → r2 acc[4]
    let p4 = bt[4] * at[4]; // β=(1,1) → r2 acc[5], r1 acc[1]
    let p5 = bt[5] * at[5]; // β=(2,1) → r1 acc[1]
    let p6 = bt[6] * at[6]; // β=(0,2) → r2 acc[6]
    let p7 = bt[7] * at[7]; // β=(1,2) → r2 acc[7]

    // Round 1 (2 accumulations): sum over β1∈{1,2} per β2
    acc[0] += p1 + p2;
    acc[1] += p4 + p5;

    // Round 2 (6 accumulations): single product per (β2, β1) with β1≤1
    acc[2] += p0;
    acc[3] += p1;
    acc[4] += p3;
    acc[5] += p4;
    acc[6] += p6;
    acc[7] += p7;
}

/// Parallel precomputation of all 8 SVO accumulators.
/// Returns reduced `EF` values (summed over SIMD lanes).
fn precompute_svo_accumulators<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    n_block: usize,
) -> [EF; N_ACCUM] {
    let zero_acc = || [EFPacking::<EF>::ZERO; N_ACCUM];

    let packed_acc: [EFPacking<EF>; N_ACCUM] = if n_block < PARALLEL_THRESHOLD {
        let mut acc = zero_acc();
        for i in 0..n_block {
            process_svo_block::<EF>(i, evals, weights, n_block, &mut acc);
        }
        acc
    } else {
        (0..n_block)
            .into_par_iter()
            .fold(zero_acc, |mut acc, i| {
                process_svo_block::<EF>(i, evals, weights, n_block, &mut acc);
                acc
            })
            .reduce(zero_acc, |mut a, b| {
                for k in 0..N_ACCUM {
                    a[k] += b[k];
                }
                a
            })
    };

    // Reduce EFPacking → EF by summing SIMD lanes
    std::array::from_fn(|k| EFPacking::<EF>::to_ext_iter([packed_acc[k]]).sum())
}

// ---------------------------------------------------------------------------
// SVO Phase 2: Round polynomials from accumulators
// ---------------------------------------------------------------------------

/// Compute the degree-2 sumcheck polynomial for SVO round `round` ∈ {1,2}.
///
/// `r_weights` has length 3^{round-1}: Lagrange weights for the folded variables.
/// Layout: round 1 → offset=0, n_v=1; round 2 → offset=2, n_v=3.
///
/// s(∞) = Σ_v r_weights[v] · accums[offset + v*2 + 0]
/// s(0)  = Σ_v r_weights[v] · accums[offset + v*2 + 1]
/// c0=s(0), c2=s(∞), c1 = sum - 2·c0 - c2  (from s(0)+s(1)=sum constraint)
fn compute_svo_round_poly<EF: Field>(
    accums: &[EF; N_ACCUM],
    r_weights: &[EF],
    round: usize,
    sum: EF,
) -> DensePolynomial<EF> {
    let offset = [0usize, 2][round - 1];
    let n_v = r_weights.len(); // 1, 3, or 9

    let mut s_inf = EF::ZERO;
    let mut s_zero = EF::ZERO;
    for v in 0..n_v {
        s_inf += r_weights[v] * accums[offset + v * 2];
        s_zero += r_weights[v] * accums[offset + v * 2 + 1];
    }

    let c0 = s_zero;
    let c2 = s_inf;
    let c1 = sum - c0.double() - c2;
    DensePolynomial::new(vec![c0, c1, c2])
}

// ---------------------------------------------------------------------------
// SVO Phase 3: Materialize folded polynomials
// ---------------------------------------------------------------------------

/// Materialize EFPacking-typed pol_a_mat and pol_b_mat of size n_block by
/// taking the weighted combination of the 4 slabs using equality weights.
///
/// eq_weights[k] folds slab dimension at challenges (r1, r2) with MSB-first ordering:
///   r1 ↔ x2 = (k>>1)&1,  r2 ↔ x1 = k&1
///
/// pol_a_mat[i] = Σ_k eq_weights[k] · evals[k·n_block + i]   (sl: EFPacking·PFPacking)
/// pol_b_mat[i] = Σ_k eq_weights[k] · weights[k·n_block + i] (ll: EFPacking·EFPacking)
fn materialize_svo_polys<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    eq_weights: [EF; N_BLOCK_FACTOR],
    n_block: usize,
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>) {
    let mut pol_a_mat = unsafe { uninitialized_vec::<EFPacking<EF>>(n_block) };
    let mut pol_b_mat = unsafe { uninitialized_vec::<EFPacking<EF>>(n_block) };

    let compute = |i: usize| -> (EFPacking<EF>, EFPacking<EF>) {
        let mut a_sum = EFPacking::<EF>::ZERO;
        let mut b_sum = EFPacking::<EF>::ZERO;
        for k in 0..N_BLOCK_FACTOR {
            let w = EFPacking::<EF>::from(eq_weights[k]);
            a_sum += w * evals[k * n_block + i]; // sl
            b_sum += w * weights[k * n_block + i]; // ll (w is EFPacking, weights[..] is EFPacking)
        }
        (a_sum, b_sum)
    };

    if n_block < PARALLEL_THRESHOLD {
        for i in 0..n_block {
            let (a, b) = compute(i);
            pol_a_mat[i] = a;
            pol_b_mat[i] = b;
        }
    } else {
        pol_a_mat
            .par_iter_mut()
            .zip(pol_b_mat.par_iter_mut())
            .enumerate()
            .for_each(|(i, (a, b))| {
                (*a, *b) = compute(i);
            });
    }

    (pol_a_mat, pol_b_mat)
}

// ---------------------------------------------------------------------------
// SVO inner prover
// ---------------------------------------------------------------------------

/// Full SVO product sumcheck prover.
///
/// Runs ELL_0=2 SVO rounds (using precomputed ternary accumulators) then
/// materializes and delegates the remaining `n_rounds - ELL_0` rounds to
/// `sumcheck_prove_many_rounds`.
fn run_product_sumcheck_svo_inner<EF: ExtensionField<PF<EF>>>(
    evals: &[PFPacking<EF>],
    weights: &[EFPacking<EF>],
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    let n = evals.len();
    let n_block = n / N_BLOCK_FACTOR;

    // Phase 1: Precompute all 8 accumulators in one pass
    let accums = precompute_svo_accumulators(evals, weights, n_block);

    // Phase 2: SVO rounds 1–ELL_0
    let mut challenges = Vec::with_capacity(n_rounds);
    // R_weights: Lagrange weights for the previously fixed ternary digits.
    // R_1 = [1], R_{i+1}[a·3 + b] = R_i[a] · w(r_i)[b]
    // where w(r) = [r·(r-1), 1-r, r] for ternary poles {∞, 0, 1}.
    let mut r_weights = vec![EF::ONE];

    for round in 1..=ELL_0 {
        let poly = compute_svo_round_poly(&accums, &r_weights, round, sum);
        prover_state.add_sumcheck_polynomial(&poly.coeffs, None);
        prover_state.pow_grinding(pow_bits);
        let r: EF = prover_state.sample();
        sum = poly.evaluate(r);
        challenges.push(r);

        // Update r_weights: tensor product with w(r)
        let w = [r * (r - EF::ONE), EF::ONE - r, r];
        let old = r_weights;
        r_weights = Vec::with_capacity(old.len() * 3);
        for rv in &old {
            for &wi in &w {
                r_weights.push(*rv * wi);
            }
        }
    }

    // Phase 3: Materialize folded pol_a and pol_b
    // eq_weights[k]: MSB-first fold — r1 ↔ x2=(k>>1)&1, r2 ↔ x1=k&1
    let r1 = challenges[0];
    let r2 = challenges[1];
    let eq_weights: [EF; N_BLOCK_FACTOR] = std::array::from_fn(|k| {
        let w2 = if (k >> 1) & 1 == 0 { EF::ONE - r1 } else { r1 };
        let w1 = if k & 1 == 0 { EF::ONE - r2 } else { r2 };
        w2 * w1
    });

    let (pol_a_mat, pol_b_mat) = materialize_svo_polys(evals, weights, eq_weights, n_block);

    // Run remaining rounds on the materialized ExtensionPacked polynomials
    let (remaining_challenges, folds, final_sum) = sumcheck_prove_many_rounds(
        MleGroupOwned::ExtensionPacked(vec![pol_a_mat, pol_b_mat]),
        None,
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - ELL_0,
        false,
        pow_bits,
    );

    challenges.extend(remaining_challenges.0);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (MultilinearPoint(challenges), final_sum, pol_a, pol_b)
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

#[instrument(skip_all)]
pub fn run_product_sumcheck<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);

    // SVO fast path: defer pol_a binding for ELL_0 rounds using ternary accumulators
    if let (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) = (pol_a, pol_b)
        && n_rounds > ELL_0
        && evals.len() >= N_BLOCK_FACTOR
    {
        return run_product_sumcheck_svo_inner(evals, weights, prover_state, sum, n_rounds, pow_bits);
    }

    // Generic fallback: promote both polynomials to extension and delegate.
    // This path only triggers for n_rounds ≤ ELL_0 or tiny inputs.
    let group = match (pol_a, pol_b) {
        (MleRef::BasePacked(a), MleRef::ExtensionPacked(b)) => {
            MleGroupOwned::ExtensionPacked(vec![a.iter().map(|&v| EFPacking::<EF>::from(v)).collect(), b.to_vec()])
        }
        (MleRef::ExtensionPacked(a), MleRef::ExtensionPacked(b)) => {
            MleGroupOwned::ExtensionPacked(vec![a.to_vec(), b.to_vec()])
        }
        (MleRef::Base(a), MleRef::Extension(b)) => {
            MleGroupOwned::Extension(vec![a.iter().map(|&v| EF::from(v)).collect(), b.to_vec()])
        }
        (MleRef::Extension(a), MleRef::Extension(b)) => MleGroupOwned::Extension(vec![a.to_vec(), b.to_vec()]),
        _ => unimplemented!(),
    };

    let (challenges, folds, final_sum) = sumcheck_prove_many_rounds(
        group,
        None,
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds,
        false,
        pow_bits,
    );
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, final_sum, pol_a, pol_b)
}

pub fn compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync,
    EF: Field,
    EFPacking: Algebra<F> + Copy + Send + Sync,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> DensePolynomial<EF> {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());

    let num_elements = n;

    let (c0_packed, c2_packed) = if num_elements < PARALLEL_THRESHOLD {
        pol_0[..n / 2]
            .iter()
            .zip(pol_0[n / 2..].iter())
            .zip(pol_1[..n / 2].iter().zip(pol_1[n / 2..].iter()))
            .map(sumcheck_quadratic)
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        pol_0[..n / 2]
            .par_iter()
            .zip(pol_0[n / 2..].par_iter())
            .zip(pol_1[..n / 2].par_iter().zip(pol_1[n / 2..].par_iter()))
            .map(sumcheck_quadratic)
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

pub fn fold_and_compute_product_sumcheck_polynomial<
    F: PrimeCharacteristicRing + Copy + Send + Sync + 'static,
    EF: Field,
    EFPacking: Algebra<F> + From<EF> + Copy + Send + Sync + 'static,
>(
    pol_0: &[F],         // evals
    pol_1: &[EFPacking], // weights
    prev_folding_factor: EF,
    sum: EF,
    decompose: impl Fn(EFPacking) -> Vec<EF>,
) -> (DensePolynomial<EF>, Vec<Vec<EFPacking>>) {
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let prev_folding_factor_packed = EFPacking::from(prev_folding_factor);

    let mut pol_0_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };
    let mut pol_1_folded = unsafe { uninitialized_vec::<EFPacking>(n / 2) };

    #[allow(clippy::type_complexity)]
    let process_element = |(p0_prev, p0_f): (((&F, &F), (&F, &F)), (&mut EFPacking, &mut EFPacking)),
                           (p1_prev, p1_f): (
        ((&EFPacking, &EFPacking), (&EFPacking, &EFPacking)),
        (&mut EFPacking, &mut EFPacking),
    )| {
        let diff_0 = *p0_prev.1.0 - *p0_prev.0.0;
        let diff_1 = *p0_prev.1.1 - *p0_prev.0.1;
        let x_0 = prev_folding_factor_packed * diff_0 + *p0_prev.0.0;
        let x_1 = prev_folding_factor_packed * diff_1 + *p0_prev.0.1;
        *p0_f.0 = x_0;
        *p0_f.1 = x_1;

        let y_0 = prev_folding_factor_packed * (*p1_prev.1.0 - *p1_prev.0.0) + *p1_prev.0.0;
        let y_1 = prev_folding_factor_packed * (*p1_prev.1.1 - *p1_prev.0.1) + *p1_prev.0.1;
        *p1_f.0 = y_0;
        *p1_f.1 = y_1;

        sumcheck_quadratic(((&x_0, &x_1), (&y_0, &y_1)))
    };

    let (c0_packed, c2_packed) = if n < PARALLEL_THRESHOLD {
        zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .fold((EFPacking::ZERO, EFPacking::ZERO), |(a0, a2), (b0, b2)| {
                (a0 + b0, a2 + b2)
            })
    } else {
        par_zip_fold_2(pol_0, &mut pol_0_folded)
            .zip(par_zip_fold_2(pol_1, &mut pol_1_folded))
            .map(|(p0, p1)| process_element(p0, p1))
            .reduce(
                || (EFPacking::ZERO, EFPacking::ZERO),
                |(a0, a2), (b0, b2)| (a0 + b0, a2 + b2),
            )
    };

    let c0 = decompose(c0_packed).into_iter().sum::<EF>();
    let c2 = decompose(c2_packed).into_iter().sum::<EF>();
    let c1 = sum - c0.double() - c2;

    (DensePolynomial::new(vec![c0, c1, c2]), vec![pol_0_folded, pol_1_folded])
}

#[inline(always)]
pub fn sumcheck_quadratic<F, EF>(((&x_0, &x_1), (&y_0, &y_1)): ((&F, &F), (&EF, &EF))) -> (EF, EF)
where
    F: PrimeCharacteristicRing + Copy,
    EF: Algebra<F> + Copy,
{
    let constant = y_0 * x_0;
    let quadratic = (y_1 - y_0) * (x_1 - x_0);
    (constant, quadratic)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::ProverState;
    use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon2_16};

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    fn make_prover() -> ProverState<EF, koala_bear::Poseidon2KoalaBear<16>> {
        ProverState::new(default_koalabear_poseidon2_16())
    }

    fn make_test_polys(n: usize) -> (Vec<PFPacking<EF>>, Vec<EFPacking<EF>>, EF) {
        let w = packing_width::<EF>();
        let evals: Vec<PFPacking<EF>> = (0..n)
            .map(|i| PFPacking::<EF>::from_fn(|j| F::from_usize((i * w + j + 1) % 1_000_003)))
            .collect();

        let weights: Vec<EFPacking<EF>> = (0..n)
            .map(|i| {
                let vals: Vec<EF> = (0..w)
                    .map(|j| EF::from(F::from_usize((i * w + j + 7) % 999_983)))
                    .collect();
                EFPacking::<EF>::from_ext_slice(&vals)
            })
            .collect();

        // True sum: Σ_i Σ_lane evals[i][lane] * weights[i][lane]
        let mut sum = EF::ZERO;
        for (e, wt) in evals.iter().zip(weights.iter()) {
            let prod: EFPacking<EF> = *wt * *e;
            let vals: Vec<EF> =
                <EFPacking<EF> as field::PackedFieldExtension<PF<EF>, EF>>::to_ext_iter([prod]).collect();
            for v in vals {
                sum += v;
            }
        }

        (evals, weights, sum)
    }

    /// After running SVO for all variables, final_sum must equal pol_a(r) * pol_b(r).
    #[test]
    fn svo_full_round_correctness() {
        let w = packing_width::<EF>();
        // n packed elements, n_vars = log2(n * w) total scalar variables
        let n = N_BLOCK_FACTOR * w;
        let n_vars = (n * w).trailing_zeros() as usize;

        let (evals, weights, sum) = make_test_polys(n);

        let mut prover = make_prover();
        let (challenges, final_sum, pol_a, pol_b) =
            run_product_sumcheck_svo_inner(&evals, &weights, &mut prover, sum, n_vars, 0);
        assert_eq!(challenges.0.len(), n_vars);

        // After all variables are bound, each MleOwned has 1 packed element.
        // Lane 0 carries the binding result; extract it.
        let extract_first = |m: &MleOwned<EF>| -> EF {
            match m {
                MleOwned::ExtensionPacked(v) => {
                    assert_eq!(v.len(), 1);
                    <EFPacking<EF> as field::PackedFieldExtension<PF<EF>, EF>>::to_ext_iter([v[0]])
                        .next()
                        .unwrap()
                }
                MleOwned::Extension(v) => {
                    assert_eq!(v.len(), 1);
                    v[0]
                }
                _ => panic!("unexpected MleOwned variant"),
            }
        };

        let a_val = extract_first(&pol_a);
        let b_val = extract_first(&pol_b);
        assert_eq!(a_val * b_val, final_sum, "final_sum != pol_a(r) * pol_b(r)");
    }
}
