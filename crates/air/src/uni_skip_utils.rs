use multilinear_toolkit::prelude::*;
use tracing::instrument;

#[instrument(skip_all)]
pub fn matrix_next_mle_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F]) -> Vec<F> {
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
    use utils::to_big_endian_in_field;

    use crate::utils::next_mle;

    use super::*;
    type F = KoalaBear;

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
