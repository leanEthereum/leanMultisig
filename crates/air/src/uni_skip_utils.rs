use backend::*;
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
