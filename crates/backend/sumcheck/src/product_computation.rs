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

#[instrument(skip_all)]
pub fn run_product_sumcheck<EF: ExtensionField<PF<EF>>>(
    pol_a: &MleRef<'_, EF>, // evals
    pol_b: &MleRef<'_, EF>, // weights
    prover_state: &mut impl FSProver<EF>,
    mut sum: EF,
    n_rounds: usize,
    pow_bits: usize,
) -> (MultilinearPoint<EF>, EF, MleOwned<EF>, MleOwned<EF>) {
    assert!(n_rounds >= 1);
    let first_sumcheck_poly = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial_base_ext_packed::<5, _, _, _, EF>(evals, weights, sum)
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            compute_product_sumcheck_polynomial_ext_ext_packed::<PF<EF>, EFPacking<EF>, EF>(evals, weights, sum)
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            compute_product_sumcheck_polynomial(evals, weights, sum, |e| vec![e])
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&first_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r1: EF = prover_state.sample();
    sum = first_sumcheck_poly.evaluate(r1);

    if n_rounds == 1 {
        return (MultilinearPoint(vec![r1]), sum, pol_a.fold(r1), pol_b.fold(r1));
    }

    let (second_sumcheck_poly, folded) = match (pol_a, pol_b) {
        (MleRef::BasePacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::ExtensionPacked(evals), MleRef::ExtensionPacked(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| {
                    EFPacking::<EF>::to_ext_iter([e]).collect()
                });
            (second_sumcheck_poly, MleGroupOwned::ExtensionPacked(folded))
        }
        (MleRef::Base(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        (MleRef::Extension(evals), MleRef::Extension(weights)) => {
            let (second_sumcheck_poly, folded) =
                fold_and_compute_product_sumcheck_polynomial(evals, weights, r1, sum, |e| vec![e]);
            (second_sumcheck_poly, MleGroupOwned::Extension(folded))
        }
        _ => unimplemented!(),
    };

    prover_state.add_sumcheck_polynomial(&second_sumcheck_poly.coeffs, None);
    prover_state.pow_grinding(pow_bits);
    let r2: EF = prover_state.sample();
    sum = second_sumcheck_poly.evaluate(r2);

    let (mut challenges, folds, sum) = sumcheck_prove_many_rounds(
        folded,
        Some(r2),
        &ProductComputation {},
        &vec![],
        None,
        prover_state,
        sum,
        None,
        n_rounds - 2,
        false,
        pow_bits,
    );

    challenges.splice(0..0, [r1, r2]);
    let [pol_a, pol_b] = folds.split().try_into().unwrap();
    (challenges, sum, pol_a, pol_b)
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

/// Specialized version for base × extension on packed data: extracts raw u32 lanes
/// and accumulates u32×u32 products into u128/i128, skipping Montgomery reduction entirely.
/// `DIM` must equal `EF::DIMENSION`.
/// extracting raw u32 lanes to avoid Montgomery reduction.
pub fn compute_product_sumcheck_polynomial_base_ext_packed<
    const DIM: usize,
    F: PrimeField32,
    PF: PackedField<Scalar = F>,
    EFP: BasedVectorSpace<PF> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[PF],
    pol_1: &[EFP],
    sum: EF,
) -> DensePolynomial<EF> {
    assert_eq!(DIM, EF::DIMENSION);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let half = n / 2;
    let width = PF::WIDTH;

    type Acc<const D: usize> = ([u128; D], [i128; D]);

    #[inline(always)]
    fn accumulate_chunk_packed<
        const D: usize,
        F: PrimeField32,
        PF: PackedField<Scalar = F>,
        EFP: BasedVectorSpace<PF>,
    >(
        c0: &mut [u128; D],
        c2: &mut [i128; D],
        base_lo: &[PF],
        base_hi: &[PF],
        ext_lo: &[EFP],
        ext_hi: &[EFP],
    ) {
        for i in 0..base_lo.len() {
            let x0_lanes = base_lo[i].as_slice();
            let x1_lanes = base_hi[i].as_slice();
            let y0_coords = ext_lo[i].as_basis_coefficients_slice();
            let y1_coords = ext_hi[i].as_basis_coefficients_slice();
            for j in 0..D {
                let y0_j = y0_coords[j].as_slice();
                let y1_j = y1_coords[j].as_slice();
                for lane in 0..PF::WIDTH {
                    let x0 = x0_lanes[lane].to_unique_u32() as u64;
                    let y0 = y0_j[lane].to_unique_u32();
                    let y1 = y1_j[lane].to_unique_u32();
                    c0[j] += (y0 as u64 * x0) as u128;
                    c2[j] +=
                        (y1 as i64 - y0 as i64) as i128 * (x1_lanes[lane].to_unique_u32() as i64 - x0 as i64) as i128;
                }
            }
        }
    }

    let zero = || ([0u128; DIM], [0i128; DIM]);

    #[inline(always)]
    fn add_acc<const D: usize>((mut a0, mut a2): Acc<D>, (b0, b2): Acc<D>) -> Acc<D> {
        for j in 0..D {
            a0[j] += b0[j];
            a2[j] += b2[j];
        }
        (a0, a2)
    }

    let chunk_size = 1024 / F::Packing::WIDTH;

    let (c0_acc, c2_acc) = if n < PARALLEL_THRESHOLD / F::Packing::WIDTH {
        let mut c0 = [0u128; DIM];
        let mut c2 = [0i128; DIM];
        accumulate_chunk_packed::<DIM, F, PF, EFP>(
            &mut c0,
            &mut c2,
            &pol_0[..half],
            &pol_0[half..],
            &pol_1[..half],
            &pol_1[half..],
        );
        (c0, c2)
    } else {
        pol_0[..half]
            .par_chunks(chunk_size)
            .zip(pol_0[half..].par_chunks(chunk_size))
            .zip(
                pol_1[..half]
                    .par_chunks(chunk_size)
                    .zip(pol_1[half..].par_chunks(chunk_size)),
            )
            .map(|((b_lo, b_hi), (e_lo, e_hi))| {
                let mut c0 = [0u128; DIM];
                let mut c2 = [0i128; DIM];
                accumulate_chunk_packed::<DIM, F, PF, EFP>(&mut c0, &mut c2, b_lo, b_hi, e_lo, e_hi);
                (c0, c2)
            })
            .reduce(zero, add_acc)
    };

    let c0 = EF::from_basis_coefficients_fn(|j| F::reduce_product_sum(c0_acc[j]));
    let c2 = EF::from_basis_coefficients_fn(|j| F::reduce_signed_product_sum(c2_acc[j]));
    let c1 = sum - c0.double() - c2;

    DensePolynomial::new(vec![c0, c1, c2])
}

/// Specialized ext×ext on NEON packed data. Computes 9 unreduced polynomial-product
/// coefficients using `vmull_u32`/`vmlal_u32` (no Montgomery reduction in inner loop),
/// then reduces mod X^5+X^2−1 with the bias trick.
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub fn compute_product_sumcheck_polynomial_ext_ext_packed<
    F: PrimeField32,
    EFP: BasedVectorSpace<F::Packing> + Copy + Send + Sync,
    EF: Field + BasedVectorSpace<F>,
>(
    pol_0: &[EFP],
    pol_1: &[EFP],
    sum: EF,
) -> DensePolynomial<EF> {
    use core::arch::aarch64::*;
    assert_eq!(5, EF::DIMENSION);
    assert_eq!(4, F::Packing::WIDTH);
    let n = pol_0.len();
    assert_eq!(n, pol_1.len());
    assert!(n.is_power_of_two());
    let half = n / 2;
    let bias: u128 = (1u128 << 90) / F::ORDER_U32 as u128 * F::ORDER_U32 as u128;

    type Acc = ([u128; 9], [u128; 9]);

    /// Flush a pair of uint64x2_t (lo 2 lanes + hi 2 lanes) into a u128 accumulator.
    #[inline(always)]
    unsafe fn flush_u(acc: &mut u128, lo: uint64x2_t, hi: uint64x2_t) {
        *acc += vgetq_lane_u64(lo, 0) as u128
            + vgetq_lane_u64(lo, 1) as u128
            + vgetq_lane_u64(hi, 0) as u128
            + vgetq_lane_u64(hi, 1) as u128;
    }

    /// Flush a pair of int64x2_t with bias into a u128 accumulator.
    #[inline(always)]
    unsafe fn flush_s(acc: &mut u128, lo: int64x2_t, hi: int64x2_t, bias: u128) {
        let sum = vgetq_lane_s64(lo, 0) as i128
            + vgetq_lane_s64(lo, 1) as i128
            + vgetq_lane_s64(hi, 0) as i128
            + vgetq_lane_s64(hi, 1) as i128;
        *acc += (bias as i128 + sum) as u128;
    }

    /// NEON: compute 9 unreduced poly coefficients of a*b using vmull/vmlal.
    /// p[4] (5 terms) split into 4+1 since 5*(P-1)² overflows u64.
    #[inline(always)]
    unsafe fn poly_product_neon(p: &mut [u128; 9], a: [uint32x4_t; 5], b: [uint32x4_t; 5]) {
        let al: [uint32x2_t; 5] = core::array::from_fn(|i| vget_low_u32(a[i]));
        let ah: [uint32x2_t; 5] = core::array::from_fn(|i| vget_high_u32(a[i]));
        let bl: [uint32x2_t; 5] = core::array::from_fn(|i| vget_low_u32(b[i]));
        let bh: [uint32x2_t; 5] = core::array::from_fn(|i| vget_high_u32(b[i]));

        // p0: a0*b0
        let lo = vmull_u32(al[0], bl[0]);
        let hi = vmull_u32(ah[0], bh[0]);
        flush_u(&mut p[0], lo, hi);
        // p1: a0*b1 + a1*b0
        let lo = vmlal_u32(vmull_u32(al[0], bl[1]), al[1], bl[0]);
        let hi = vmlal_u32(vmull_u32(ah[0], bh[1]), ah[1], bh[0]);
        flush_u(&mut p[1], lo, hi);
        // p2: 3 terms
        let lo = vmlal_u32(vmlal_u32(vmull_u32(al[0], bl[2]), al[1], bl[1]), al[2], bl[0]);
        let hi = vmlal_u32(vmlal_u32(vmull_u32(ah[0], bh[2]), ah[1], bh[1]), ah[2], bh[0]);
        flush_u(&mut p[2], lo, hi);
        // p3: 4 terms
        let lo = vmlal_u32(
            vmlal_u32(vmlal_u32(vmull_u32(al[0], bl[3]), al[1], bl[2]), al[2], bl[1]),
            al[3],
            bl[0],
        );
        let hi = vmlal_u32(
            vmlal_u32(vmlal_u32(vmull_u32(ah[0], bh[3]), ah[1], bh[2]), ah[2], bh[1]),
            ah[3],
            bh[0],
        );
        flush_u(&mut p[3], lo, hi);
        // p4: 5 terms = 4+1
        let lo = vmlal_u32(
            vmlal_u32(vmlal_u32(vmull_u32(al[0], bl[4]), al[1], bl[3]), al[2], bl[2]),
            al[3],
            bl[1],
        );
        let hi = vmlal_u32(
            vmlal_u32(vmlal_u32(vmull_u32(ah[0], bh[4]), ah[1], bh[3]), ah[2], bh[2]),
            ah[3],
            bh[1],
        );
        flush_u(&mut p[4], lo, hi);
        let lo = vmull_u32(al[4], bl[0]);
        let hi = vmull_u32(ah[4], bh[0]);
        flush_u(&mut p[4], lo, hi);
        // p5: 4 terms
        let lo = vmlal_u32(
            vmlal_u32(vmlal_u32(vmull_u32(al[1], bl[4]), al[2], bl[3]), al[3], bl[2]),
            al[4],
            bl[1],
        );
        let hi = vmlal_u32(
            vmlal_u32(vmlal_u32(vmull_u32(ah[1], bh[4]), ah[2], bh[3]), ah[3], bh[2]),
            ah[4],
            bh[1],
        );
        flush_u(&mut p[5], lo, hi);
        // p6: 3 terms
        let lo = vmlal_u32(vmlal_u32(vmull_u32(al[2], bl[4]), al[3], bl[3]), al[4], bl[2]);
        let hi = vmlal_u32(vmlal_u32(vmull_u32(ah[2], bh[4]), ah[3], bh[3]), ah[4], bh[2]);
        flush_u(&mut p[6], lo, hi);
        // p7: 2 terms
        let lo = vmlal_u32(vmull_u32(al[3], bl[4]), al[4], bl[3]);
        let hi = vmlal_u32(vmull_u32(ah[3], bh[4]), ah[4], bh[3]);
        flush_u(&mut p[7], lo, hi);
        // p8: 1 term
        let lo = vmull_u32(al[4], bl[4]);
        let hi = vmull_u32(ah[4], bh[4]);
        flush_u(&mut p[8], lo, hi);
    }

    /// Same for signed (int32) differences using vmull_s32/vmlal_s32.
    /// Max 2 products per accumulation to avoid i64 overflow (2*(P-1)² < i64::MAX).
    #[inline(always)]
    unsafe fn poly_product_signed_neon(p: &mut [u128; 9], a: [int32x4_t; 5], b: [int32x4_t; 5], bias: u128) {
        let al: [int32x2_t; 5] = core::array::from_fn(|i| vget_low_s32(a[i]));
        let ah: [int32x2_t; 5] = core::array::from_fn(|i| vget_high_s32(a[i]));
        let bl: [int32x2_t; 5] = core::array::from_fn(|i| vget_low_s32(b[i]));
        let bh: [int32x2_t; 5] = core::array::from_fn(|i| vget_high_s32(b[i]));

        // p0: 1 term
        let lo = vmull_s32(al[0], bl[0]);
        let hi = vmull_s32(ah[0], bh[0]);
        flush_s(&mut p[0], lo, hi, bias);
        // p1: 2 terms — ok
        let lo = vmlal_s32(vmull_s32(al[0], bl[1]), al[1], bl[0]);
        let hi = vmlal_s32(vmull_s32(ah[0], bh[1]), ah[1], bh[0]);
        flush_s(&mut p[1], lo, hi, bias);
        // p2: 3 terms — split 2+1
        let lo = vmlal_s32(vmull_s32(al[0], bl[2]), al[1], bl[1]);
        let hi = vmlal_s32(vmull_s32(ah[0], bh[2]), ah[1], bh[1]);
        flush_s(&mut p[2], lo, hi, bias);
        let lo = vmull_s32(al[2], bl[0]);
        let hi = vmull_s32(ah[2], bh[0]);
        flush_s(&mut p[2], lo, hi, bias);
        // p3: 4 terms — split 2+2
        let lo = vmlal_s32(vmull_s32(al[0], bl[3]), al[1], bl[2]);
        let hi = vmlal_s32(vmull_s32(ah[0], bh[3]), ah[1], bh[2]);
        flush_s(&mut p[3], lo, hi, bias);
        let lo = vmlal_s32(vmull_s32(al[2], bl[1]), al[3], bl[0]);
        let hi = vmlal_s32(vmull_s32(ah[2], bh[1]), ah[3], bh[0]);
        flush_s(&mut p[3], lo, hi, bias);
        // p4: 5 terms — split 2+2+1
        let lo = vmlal_s32(vmull_s32(al[0], bl[4]), al[1], bl[3]);
        let hi = vmlal_s32(vmull_s32(ah[0], bh[4]), ah[1], bh[3]);
        flush_s(&mut p[4], lo, hi, bias);
        let lo = vmlal_s32(vmull_s32(al[2], bl[2]), al[3], bl[1]);
        let hi = vmlal_s32(vmull_s32(ah[2], bh[2]), ah[3], bh[1]);
        flush_s(&mut p[4], lo, hi, bias);
        let lo = vmull_s32(al[4], bl[0]);
        let hi = vmull_s32(ah[4], bh[0]);
        flush_s(&mut p[4], lo, hi, bias);
        // p5: 4 terms — split 2+2
        let lo = vmlal_s32(vmull_s32(al[1], bl[4]), al[2], bl[3]);
        let hi = vmlal_s32(vmull_s32(ah[1], bh[4]), ah[2], bh[3]);
        flush_s(&mut p[5], lo, hi, bias);
        let lo = vmlal_s32(vmull_s32(al[3], bl[2]), al[4], bl[1]);
        let hi = vmlal_s32(vmull_s32(ah[3], bh[2]), ah[4], bh[1]);
        flush_s(&mut p[5], lo, hi, bias);
        // p6: 3 terms — split 2+1
        let lo = vmlal_s32(vmull_s32(al[2], bl[4]), al[3], bl[3]);
        let hi = vmlal_s32(vmull_s32(ah[2], bh[4]), ah[3], bh[3]);
        flush_s(&mut p[6], lo, hi, bias);
        let lo = vmull_s32(al[4], bl[2]);
        let hi = vmull_s32(ah[4], bh[2]);
        flush_s(&mut p[6], lo, hi, bias);
        // p7: 2 terms — ok
        let lo = vmlal_s32(vmull_s32(al[3], bl[4]), al[4], bl[3]);
        let hi = vmlal_s32(vmull_s32(ah[3], bh[4]), ah[4], bh[3]);
        flush_s(&mut p[7], lo, hi, bias);

        let lo = vmull_s32(al[4], bl[4]);
        let hi = vmull_s32(ah[4], bh[4]);
        flush_s(&mut p[8], lo, hi, bias);
    }

    #[inline(always)]
    fn accumulate_chunk<F: PrimeField32, EFP: BasedVectorSpace<F::Packing>>(
        c0: &mut [u128; 9],
        c2: &mut [u128; 9],
        a_lo: &[EFP],
        a_hi: &[EFP],
        b_lo: &[EFP],
        b_hi: &[EFP],
        bias: u128,
    ) {
        unsafe {
            for i in 0..a_lo.len() {
                let x0c = a_lo[i].as_basis_coefficients_slice();
                let x1c = a_hi[i].as_basis_coefficients_slice();
                let y0c = b_lo[i].as_basis_coefficients_slice();
                let y1c = b_hi[i].as_basis_coefficients_slice();

                // Load as uint32x4_t via pointer cast (repr(transparent) guarantees layout)
                let x0: [uint32x4_t; 5] = core::array::from_fn(|j| vld1q_u32(x0c[j].as_slice().as_ptr() as *const u32));
                let y0: [uint32x4_t; 5] = core::array::from_fn(|j| vld1q_u32(y0c[j].as_slice().as_ptr() as *const u32));

                poly_product_neon(c0, x0, y0);

                // dx = x1 - x0, dy = y1 - y0 as signed int32x4
                let dx: [int32x4_t; 5] = core::array::from_fn(|j| {
                    let x1 = vld1q_u32(x1c[j].as_slice().as_ptr() as *const u32);
                    vreinterpretq_s32_u32(vsubq_u32(x1, x0[j]))
                });
                let dy: [int32x4_t; 5] = core::array::from_fn(|j| {
                    let y1 = vld1q_u32(y1c[j].as_slice().as_ptr() as *const u32);
                    vreinterpretq_s32_u32(vsubq_u32(y1, y0[j]))
                });

                poly_product_signed_neon(c2, dx, dy, bias);
            }
        }
    }

    let zero = || ([0u128; 9], [0u128; 9]);

    fn add_acc((mut a0, mut a2): Acc, (b0, b2): Acc) -> Acc {
        for j in 0..9 {
            a0[j] += b0[j];
            a2[j] += b2[j];
        }
        (a0, a2)
    }

    let chunk_size = 256; // tuned for NEON register pressure

    let (c0_poly, c2_poly) = if n < PARALLEL_THRESHOLD / 4 {
        let mut c0 = [0u128; 9];
        let mut c2 = [0u128; 9];
        accumulate_chunk::<F, EFP>(
            &mut c0,
            &mut c2,
            &pol_0[..half],
            &pol_0[half..],
            &pol_1[..half],
            &pol_1[half..],
            bias,
        );
        (c0, c2)
    } else {
        pol_0[..half]
            .par_chunks(chunk_size)
            .zip(pol_0[half..].par_chunks(chunk_size))
            .zip(
                pol_1[..half]
                    .par_chunks(chunk_size)
                    .zip(pol_1[half..].par_chunks(chunk_size)),
            )
            .map(|((a_lo, a_hi), (b_lo, b_hi))| {
                let mut c0 = [0u128; 9];
                let mut c2 = [0u128; 9];
                accumulate_chunk::<F, EFP>(&mut c0, &mut c2, a_lo, a_hi, b_lo, b_hi, bias);
                (c0, c2)
            })
            .reduce(zero, add_acc)
    };

    // Reduce mod X^5 + X^2 - 1: X^5 = 1 - X^2
    let reduce_poly = |p: &[u128; 9]| -> EF {
        let r = [
            p[0] + p[5] + bias - p[8],
            p[1] + p[6],
            p[2] + p[7] + p[8] + bias - p[5],
            p[3] + p[8] + bias - p[6],
            p[4] + bias - p[7],
        ];
        EF::from_basis_coefficients_fn(|j| F::reduce_product_sum(r[j]))
    };

    let c0 = reduce_poly(&c0_poly);
    let c2 = reduce_poly(&c2_poly);
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
