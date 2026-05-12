use field::{ExtensionField, Field, PrimeCharacteristicRing};

use crate::{PF, eval_eq_scaled};

/// Evaluates the "next" multilinear polynomial at two n-variable points (x, y).
///
/// On boolean inputs, returns 1 if y = x + 1 (big-endian binary), with the special case that
/// next_mle(2^n - 1, 2^n - 1) = 1 (wrap-around).
pub fn next_mle<F: Field>(x: &[F], y: &[F]) -> F {
    assert_eq!(x.len(), y.len());
    let n = x.len();
    let mut eq_prefix = Vec::with_capacity(n + 1);
    eq_prefix.push(F::ONE);
    for i in 0..n {
        let eq_i = x[i] * y[i] + (F::ONE - x[i]) * (F::ONE - y[i]);
        eq_prefix.push(eq_prefix[i] * eq_i);
    }
    let mut low_suffix = vec![F::ONE; n + 1];
    for i in (0..n).rev() {
        low_suffix[i] = low_suffix[i + 1] * x[i] * (F::ONE - y[i]);
    }
    let mut sum = F::ZERO;
    for arr in 0..n {
        let carry = (F::ONE - x[arr]) * y[arr];
        sum += eq_prefix[arr] * carry * low_suffix[arr + 1];
    }

    sum + x.iter().chain(y).copied().product::<F>()
}

/// Computes the dense vector `next_mle(outer_challenges, y)` for all y in {0,1}^n.
///
/// This is the "folded" version: the first argument (outer_challenges) is fixed,
/// and the result is a vector indexed by the second argument.
pub fn matrix_next_mle_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F]) -> Vec<F>
where
    PF<F>: PrimeCharacteristicRing,
{
    let n = outer_challenges.len();
    let mut res = F::zero_vec(1 << n);
    for k in 0..n {
        let outer_challenges_prod =
            (F::ONE - outer_challenges[n - k - 1]) * outer_challenges[n - k..].iter().copied().product::<F>();
        let mut eq_mle = eval_eq_scaled(&outer_challenges[0..n - k - 1], outer_challenges_prod);
        for (mut i, v) in eq_mle.iter_mut().enumerate() {
            i <<= k + 1;
            i += 1 << k;
            res[i] += *v;
        }
    }
    res[(1 << n) - 1] += outer_challenges.iter().copied().product::<F>();

    res
}

#[cfg(test)]
mod tests {
    use field::PrimeCharacteristicRing;
    use goldilocks::Goldilocks;

    use crate::{EvaluationsList, MultilinearPoint, matrix_next_mle_folded, next_mle, to_big_endian_in_field};

    type F = Goldilocks;

    #[test]
    fn test_matrix_down_folded() {
        let n_vars = 5;
        for x in 0..1 << n_vars {
            let x_bools = to_big_endian_in_field::<F>(x, n_vars);
            let matrix = matrix_next_mle_folded(&x_bools);
            for y in 0..1 << n_vars {
                let y_bools = to_big_endian_in_field::<F>(y, n_vars);
                let expected = F::from_bool(if (x, y) == ((1 << n_vars) - 1, (1 << n_vars) - 1) {
                    true
                } else {
                    x + 1 == y
                });
                assert_eq!(matrix.evaluate(&MultilinearPoint(y_bools.clone())), expected);
                assert_eq!(next_mle(&x_bools, &y_bools), expected);
            }
        }
    }
}
