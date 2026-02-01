use std::borrow::Borrow;

use crate::from_end;
use p3_util::log2_strict_usize;

use multilinear_toolkit::prelude::*;
use tracing::instrument;

#[instrument(skip_all)]
pub fn multilinears_linear_combination<F: Field, EF: ExtensionField<F>, P: Borrow<[F]> + Send + Sync>(
    pols: &[P],
    scalars: &[EF],
) -> Vec<EF> {
    assert_eq!(pols.len(), scalars.len());
    let n_vars = log2_strict_usize(pols[0].borrow().len());
    assert!(pols.iter().all(|p| log2_strict_usize(p.borrow().len()) == n_vars));
    (0..1 << n_vars)
        .into_par_iter()
        .map(|i| dot_product(scalars.iter().copied(), pols.iter().map(|p| p.borrow()[i])))
        .collect::<Vec<_>>()
}

pub fn multilinear_eval_constants_at_right<F: Field>(limit: usize, point: &[F]) -> F {
    let n_vars = point.len();

    // multilinear polynomial = [0 0 --- 0][1 1 --- 1] (`limit` times 0, then `2^n_vars - limit` times 1) evaluated at `point`

    assert!(limit <= (1 << n_vars), "limit {limit} is too large for n_vars {n_vars}");

    if limit == 1 << n_vars {
        return F::ZERO;
    }

    if point.is_empty() {
        assert!(limit <= 1);
        if limit == 1 { F::ZERO } else { F::ONE }
    } else {
        let main_bit = limit >> (n_vars - 1);
        if main_bit == 1 {
            // limit is at the right half
            point[0] * multilinear_eval_constants_at_right(limit - (1 << (n_vars - 1)), &point[1..])
        } else {
            // limit is at left half
            point[0] + (F::ONE - point[0]) * multilinear_eval_constants_at_right(limit, &point[1..])
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

pub fn padd_with_zero_to_next_power_of_two<F: Field>(pol: &[F]) -> Vec<F> {
    padd_to_next_power_of_two(pol, F::ZERO)
}

pub fn padd_to_next_power_of_two<F: Field>(pol: &[F], value: F) -> Vec<F> {
    let next_power_of_two = pol.len().next_power_of_two();
    let mut padded = pol.to_vec();
    padded.resize(next_power_of_two, value);
    padded
}

pub fn padd_with_zero_to_next_multiple_of<F: Field>(pol: &[F], multiple: usize) -> Vec<F> {
    let next_multiple = pol.len().next_multiple_of(multiple);
    let mut padded = pol.to_vec();
    padded.resize(next_multiple, F::ZERO);
    padded
}

pub fn evaluate_as_larger_multilinear_pol<F: Field, EF: ExtensionField<F>>(pol: &[F], point: &[EF]) -> EF {
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

pub fn evaluate_as_smaller_multilinear_pol<F: Field, EF: ExtensionField<F>>(pol: &[F], point: &[EF]) -> EF {
    let pol_n_vars = log2_strict_usize(pol.len());
    assert!(point.len() <= pol_n_vars);
    (&pol[..1 << point.len()]).evaluate(&MultilinearPoint(point.to_vec()))
}

#[must_use]
pub fn fold_multilinear_chunks<F: Field, EF: ExtensionField<F>>(
    poly: &[F],
    folding_randomness: &MultilinearPoint<EF>,
) -> Vec<EF> {
    let folding_factor = folding_randomness.num_variables();
    poly.par_chunks_exact(1 << folding_factor)
        .map(|ev| ev.evaluate(folding_randomness))
        .collect()
}

pub fn mle_of_01234567_etc<F: Field>(point: &[F]) -> F {
    if point.is_empty() {
        F::ZERO
    } else {
        let e = mle_of_01234567_etc(&point[1..]);
        (F::ONE - point[0]) * e + point[0] * (e + F::from_usize(1 << (point.len() - 1)))
    }
}

/// table = 0 is reversed for memory lookup
pub const MEMORY_TABLE_INDEX: usize = 0;
/// table = 1 is reversed for bytecode lookup
pub const BYTECODE_TABLE_INDEX: usize = 1;
/// All the remaining tables come after memory and bytecode (special cases)
pub const FIRST_NORMAL_TABLE_INDEX: usize = 2;

pub fn finger_print<F: Field, IF: ExtensionField<PF<EF>>, EF: ExtensionField<IF> + ExtensionField<F>>(
    table: F,
    data: &[IF],
    alphas_eq_poly: &[EF],
) -> EF {
    assert!(alphas_eq_poly.len() > data.len());
    alphas_eq_poly[0] * table + dot_product::<EF, _, _>(alphas_eq_poly[1..].iter().copied(), data.iter().copied())
}

#[cfg(test)]
mod tests {
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
        pol.iter_mut().take(1 << n_vars).for_each(|coeff| *coeff = rng.random());
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
            pol.iter_mut()
                .take(1 << n_vars)
                .skip(limit)
                .for_each(|coeff| *coeff = F::ONE);
            assert_eq!(eval, pol.evaluate(&MultilinearPoint(point.clone())));
        }
    }

    #[test]
    fn test_mle_of_01234567_etc() {
        let n_vars = 10;
        let mut rng = StdRng::seed_from_u64(0);
        let point = (0..n_vars).map(|_| rng.random()).collect::<Vec<F>>();
        let eval = mle_of_01234567_etc(&point);
        let mut pol = F::zero_vec(1 << n_vars);
        for (i, p) in pol.iter_mut().enumerate().take(1 << n_vars) {
            *p = F::from_usize(i);
        }
        assert_eq!(eval, pol.evaluate(&MultilinearPoint(point)));
    }
}
