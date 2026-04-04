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
