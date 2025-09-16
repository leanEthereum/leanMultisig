use std::borrow::Borrow;

use crate::from_end;
use p3_field::{BasedVectorSpace, PackedValue};
use p3_field::{ExtensionField, Field, dot_product};
use p3_util::log2_strict_usize;
use rayon::prelude::*;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;

use crate::{EFPacking, PF};

pub fn fold_multilinear_in_small_field<F: Field, EF: ExtensionField<F>, D>(
    m: &[D],
    scalars: &[F],
) -> Vec<EF> {
    // TODO ...
    assert!(scalars.len().is_power_of_two() && scalars.len() <= m.len());
    let new_size = m.len() / scalars.len();

    let dim = <EF as BasedVectorSpace<F>>::DIMENSION;

    let m_transmuted: &[F] =
        unsafe { std::slice::from_raw_parts(std::mem::transmute(m.as_ptr()), m.len() * dim) };
    let res_transmuted = {
        let new_size = m.len() * dim / scalars.len();

        if new_size < F::Packing::WIDTH {
            (0..new_size)
                .into_par_iter()
                .map(|i| {
                    scalars
                        .iter()
                        .enumerate()
                        .map(|(j, s)| *s * m_transmuted[i + j * new_size])
                        .sum()
                })
                .collect()
        } else {
            let inners = (0..scalars.len())
                .map(|i| &m_transmuted[i * new_size..(i + 1) * new_size])
                .collect::<Vec<_>>();
            let inners_packed = inners
                .iter()
                .map(|&inner| F::Packing::pack_slice(inner))
                .collect::<Vec<_>>();

            let packed_res = (0..new_size / F::Packing::WIDTH)
                .into_par_iter()
                .map(|i| {
                    scalars
                        .iter()
                        .enumerate()
                        .map(|(j, s)| inners_packed[j][i] * *s)
                        .sum::<F::Packing>()
                })
                .collect::<Vec<_>>();

            let mut unpacked: Vec<F> = unsafe { std::mem::transmute(packed_res) };
            unsafe {
                unpacked.set_len(new_size);
            }

            unpacked
        }
    };
    let res: Vec<EF> = unsafe {
        let mut res: Vec<EF> = std::mem::transmute(res_transmuted);
        res.set_len(new_size);
        res
    };

    res
}

pub fn fold_multilinear_in_large_field<F: Field, EF: ExtensionField<F>>(
    m: &[F],
    scalars: &[EF],
) -> Vec<EF> {
    assert!(scalars.len().is_power_of_two() && scalars.len() <= m.len());
    let new_size = m.len() / scalars.len();
    (0..new_size)
        .into_par_iter()
        .map(|i| {
            scalars
                .iter()
                .enumerate()
                .map(|(j, s)| *s * m[i + j * new_size])
                .sum()
        })
        .collect()
}

pub fn fold_extension_packed<EF: ExtensionField<PF<EF>>>(
    m: &[EFPacking<EF>],
    scalars: &[EF],
) -> Vec<EFPacking<EF>> {
    assert!(scalars.len().is_power_of_two() && scalars.len() <= m.len());
    let new_size = m.len() / scalars.len();

    (0..new_size)
        .into_par_iter()
        .map(|i| {
            scalars
                .iter()
                .enumerate()
                .map(|(j, s)| m[i + j * new_size] * *s)
                .sum()
        })
        .collect()
}

pub fn multilinears_linear_combination<
    F: Field,
    EF: ExtensionField<F>,
    P: Borrow<[F]> + Send + Sync,
>(
    pols: &[P],
    scalars: &[EF],
) -> Vec<EF> {
    assert_eq!(pols.len(), scalars.len());
    let n_vars = pols[0].borrow().num_variables();
    assert!(pols.iter().all(|p| p.borrow().num_variables() == n_vars));
    (0..1 << n_vars)
        .into_par_iter()
        .map(|i| dot_product(scalars.iter().copied(), pols.iter().map(|p| p.borrow()[i])))
        .collect::<Vec<_>>()
}

pub fn batch_fold_multilinear_in_large_field<F: Field, EF: ExtensionField<F>>(
    polys: &[&[F]],
    scalars: &[EF],
) -> Vec<Vec<EF>> {
    polys
        .par_iter()
        .map(|poly| fold_multilinear_in_large_field(poly, scalars))
        .collect()
}

pub fn batch_fold_multilinear_in_large_field_packed<EF: ExtensionField<PF<EF>>>(
    polys: &[&[EFPacking<EF>]],
    scalars: &[EF],
) -> Vec<Vec<EFPacking<EF>>> {
    polys
        .iter()
        .map(|poly| fold_extension_packed(poly, scalars))
        .collect()
}

pub fn batch_fold_multilinear_in_small_field<F: Field, EF: ExtensionField<F>>(
    polys: &[&[EF]],
    scalars: &[F],
) -> Vec<Vec<EF>> {
    polys
        .par_iter()
        .map(|poly| fold_multilinear_in_small_field(poly, scalars))
        .collect()
}

pub fn batch_fold_multilinear_in_small_field_packed<EF: ExtensionField<PF<EF>>>(
    polys: &[&[EFPacking<EF>]],
    scalars: &[PF<EF>],
) -> Vec<Vec<EF>> {
    polys
        .par_iter()
        .map(|poly| fold_multilinear_in_small_field(poly, scalars))
        .collect()
}

pub fn multilinear_eval_constants_at_right<F: Field>(limit: usize, point: &[F]) -> F {
    let n_vars = point.len();

    // multilinear polynomial = [0 0 --- 0][1 1 --- 1] (`limit` times 0, then `2^n_vars - limit` times 1) evaluated at `point`

    assert!(
        limit <= (1 << n_vars),
        "limit {} is too large for n_vars {}",
        limit,
        n_vars
    );

    if limit == 1 << n_vars {
        return F::ZERO;
    }

    if point.len() == 0 {
        assert!(limit <= 1);
        if limit == 1 { F::ZERO } else { F::ONE }
    } else {
        let main_bit = limit >> (n_vars - 1);
        if main_bit == 1 {
            // limit is at the right half
            return point[0]
                * multilinear_eval_constants_at_right(limit - (1 << (n_vars - 1)), &point[1..]);
        } else {
            // limit is at left half
            return point[0]
                + (F::ONE - point[0]) * multilinear_eval_constants_at_right(limit, &point[1..]);
        }
    }
}

// pub fn packed_multilinear<F: Field>(pols: &[Vec<F>]) -> Vec<F> {
//     let n_vars = pols[0].num_variables();
//     assert!(pols.iter().all(|p| p.num_variables() == n_vars));
//     let packed_len = (pols.len() << n_vars).next_power_of_two();
//     let mut dst = F::zero_vec(packed_len);
//     let mut offset = 0;
//     // TODO parallelize
//     for pol in pols {
//         dst[offset..offset + pol.num_evals()].copy_from_slice(pol);
//         offset += pol.num_evals();
//     }
//     dst
// }

pub fn add_multilinears<F: Field>(pol1: &[F], pol2: &[F]) -> Vec<F> {
    assert_eq!(pol1.len(), pol2.len());
    let mut dst = pol1.to_vec();
    dst.par_iter_mut()
        .zip(pol2.par_iter())
        .for_each(|(a, b)| *a += *b);
    dst
}

pub fn padd_with_zero_to_next_power_of_two<F: Field>(pol: &[F]) -> Vec<F> {
    let next_power_of_two = pol.len().next_power_of_two();
    let mut padded = pol.to_vec();
    padded.resize(next_power_of_two, F::ZERO);
    padded
}

pub fn padd_with_zero_to_next_multiple_of<F: Field>(pol: &[F], multiple: usize) -> Vec<F> {
    let next_multiple = pol.len().next_multiple_of(multiple);
    let mut padded = pol.to_vec();
    padded.resize(next_multiple, F::ZERO);
    padded
}

pub fn evaluate_as_larger_multilinear_pol<F: Field, EF: ExtensionField<F>>(
    pol: &[F],
    point: &[EF],
) -> EF {
    // [[-pol-] 0 0 0 0 ... 0 0 0 0 0] evaluated at point
    let pol_n_vars = log2_strict_usize(pol.len());
    assert!(point.len() >= pol_n_vars);
    point
        .iter()
        .take(point.len() - pol_n_vars)
        .map(|x| EF::ONE - *x)
        .product::<EF>()
        * pol.evaluate(&MultilinearPoint(from_end(point, pol_n_vars).to_vec()))
}

pub fn evaluate_as_smaller_multilinear_pol<F: Field, EF: ExtensionField<F>>(
    pol: &[F],
    point: &[EF],
) -> EF {
    let pol_n_vars = log2_strict_usize(pol.len());
    assert!(point.len() <= pol_n_vars);
    (&pol[..1 << point.len()]).evaluate(&MultilinearPoint(point.to_vec()))
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    use super::*;

    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_evaluate_as_larger_multilinear_pol() {
        let n_vars = 5;
        let n_point_vars = 7;
        let mut rng = StdRng::seed_from_u64(0);
        let mut pol = F::zero_vec(1 << n_point_vars);
        for i in 0..(1 << n_vars) {
            pol[i] = rng.random();
        }
        let point = (0..n_point_vars).map(|_| rng.random()).collect::<Vec<EF>>();
        assert_eq!(
            evaluate_as_larger_multilinear_pol(&pol[..1 << n_vars], &point),
            pol.evaluate(&MultilinearPoint(point))
        );
    }

    #[test]
    fn test_multilinear_eval_constants_at_right() {
        let n_vars = 10;
        let mut rng = StdRng::seed_from_u64(0);
        let point = (0..n_vars).map(|_| rng.random()).collect::<Vec<F>>();
        for limit in [0, 1, 2, 45, 74, 451, 741, 1022, 1023] {
            let eval = multilinear_eval_constants_at_right(limit, &point);
            let mut pol = F::zero_vec(1 << n_vars);
            for i in limit..(1 << n_vars) {
                pol[i] = F::ONE;
            }
            assert_eq!(eval, pol.evaluate(&MultilinearPoint(point.clone())));
        }
    }
}
