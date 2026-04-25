use field::Field;

/// Evaluates the MLE of `[0, ..., 0, 1, ..., 1]` (`n_zeros` zeros, then ones) at `point`.
pub fn mle_of_zeros_then_ones<F: Field>(n_zeros: usize, point: &[F]) -> F {
    let n_values = 1 << point.len();
    assert!(n_zeros <= n_values);
    if n_zeros == 0 {
        return F::ONE;
    }
    if n_zeros == n_values {
        return F::ZERO;
    }
    let half = n_values / 2;
    if n_zeros < half {
        (F::ONE - point[0]) * mle_of_zeros_then_ones::<F>(n_zeros, &point[1..]) + point[0]
    } else {
        point[0] * mle_of_zeros_then_ones::<F>(n_zeros - half, &point[1..])
    }
}

#[cfg(test)]
mod tests {
    use crate::{EvaluationsList, MultilinearPoint};
    use field::PrimeCharacteristicRing;
    use goldilocks::Goldilocks;
    use rand::{RngExt, SeedableRng, rngs::StdRng};

    use super::*;
    type F = Goldilocks;

    #[test]
    fn test_mle_of_zeros_then_ones() {
        let mut rng = StdRng::seed_from_u64(0);
        for n_vars in 0..10 {
            for n_zeros in 0..=1 << n_vars {
                let slice = [vec![F::ZERO; n_zeros], vec![F::ONE; (1 << n_vars) - n_zeros]].concat();
                let point = (0..n_vars).map(|_| rng.random()).collect::<Vec<F>>();
                assert_eq!(
                    mle_of_zeros_then_ones::<F>(n_zeros, &point),
                    slice.evaluate(&MultilinearPoint(point))
                );
            }
        }
    }
}
