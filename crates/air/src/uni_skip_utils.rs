use multilinear_toolkit::prelude::*;
use tracing::instrument;

#[instrument(skip_all)]
pub fn matrix_up_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F], alpha: F) -> Vec<F> {
    let n = outer_challenges.len();
    let mut folded = eval_eq_scaled(outer_challenges, alpha);
    let outer_challenges_prod: F = outer_challenges.iter().copied().product();
    folded[(1 << n) - 1] -= outer_challenges_prod * alpha;
    folded[(1 << n) - 2] += outer_challenges_prod * alpha;
    folded
}

#[instrument(skip_all)]
pub fn matrix_down_folded<F: ExtensionField<PF<F>>>(outer_challenges: &[F], dest: &mut [F]) {
    let n = outer_challenges.len();
    for k in 0..n {
        let outer_challenges_prod = (F::ONE - outer_challenges[n - k - 1])
            * outer_challenges[n - k..].iter().copied().product::<F>();
        let mut eq_mle = eval_eq_scaled(&outer_challenges[0..n - k - 1], outer_challenges_prod);
        for (mut i, v) in eq_mle.iter_mut().enumerate() {
            i <<= k + 1;
            i += 1 << k;
            dest[i] += *v;
        }
    }
    // bottom left corner:
    dest[(1 << n) - 1] += outer_challenges.iter().copied().product::<F>();
}

#[cfg(test)]
mod tests {
    use utils::to_big_endian_in_field;

    use super::*;
    type F = p3_koala_bear::KoalaBear;

    #[test]
    fn test_matrix_down_folded() {
        let n_vars = 5;
        for x in 0..1 << n_vars {
            let x_bools = to_big_endian_in_field::<F>(x, n_vars);
            let mut matrix = F::zero_vec(1 << n_vars);
            matrix_down_folded(&x_bools, &mut matrix);
            for y in 0..1 << n_vars {
                let y_bools = to_big_endian_in_field::<F>(y, n_vars);
                let expected = if x == (1 << n_vars) - 1 {
                    F::from_bool(x == y)
                } else {
                    F::from_bool(x + 1 == y)
                };
                assert_eq!(matrix.evaluate(&MultilinearPoint(y_bools)), expected);
            }
        }
    }
}
