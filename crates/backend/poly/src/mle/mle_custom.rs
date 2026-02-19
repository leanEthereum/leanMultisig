use field::Field;

pub fn mle_of_zeros_then_ones<F: Field>(n_zeros: usize, point: &[F]) -> F {
    let n_vars = point.len();
    let n_values = 1 << n_vars;
    assert!(n_zeros <= n_values);
    if n_vars == 0 {
        F::from_usize(1 - n_zeros)
    } else if n_zeros < n_values / 2 {
        (F::ONE - point[0]) * mle_of_zeros_then_ones::<F>(n_zeros, &point[1..]) + point[0]
    } else {
        point[0] * mle_of_zeros_then_ones::<F>(n_zeros - n_values / 2, &point[1..])
    }
}

#[cfg(test)]
mod tests {
    use crate::{EvaluationsList, MultilinearPoint};
    use field::PrimeCharacteristicRing;
    use koala_bear::KoalaBear;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;
    type F = KoalaBear;

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
