use backend::*;

/// Returns a multilinear polynomial in 2n variables that evaluates to 1
/// if and only if the second n-bit vector is equal to the first vector plus one (viewed as big-endian integers).
///
/// (0 1 0 0 ... 0 0 0)
/// (0 0 1 0 ... 0 0 0)
/// (0 0 0 1 ... 0 0 0)
/// (0 0 0 0 ... 0 0 0)
/// (0 0 0 0 ... 0 0 0)
/// ...      ...   ...
/// (0 0 0 0 ... 0 1 0)
/// (0 0 0 0 ... 0 0 1)
/// (0 0 0 0 ... 0 0 1)
///
/// # Arguments
/// - `point`: A slice of 2n field elements representing two n-bit vectors concatenated.
///   The first n elements are `x` (original vector), the last n are `y` (candidate successor).
///
/// # Behavior
/// Constructs a polynomial P(x, y) such that:
/// \begin{equation}
///     P(x, y) = 1 \quad \text{if and only if} \quad y = x + 1.
/// \end{equation}
///
/// The polynomial sums contributions for each possible carry position `k`,
/// ensuring that:
/// 1. Bits to the left of `k` (more significant) match.
/// 2. Bit at position `k` transitions from 0 (in x) to 1 (in y).
/// 3. Bits to the right of `k` are 1 in x and 0 in y (simulating the carry propagation).
///
/// # Panics
/// Panics if `point.len()` is not even.
///
/// # Returns
/// Field element: 1 if y = x + 1, 0 otherwise.
pub(crate) fn next_mle<F: Field>(x: &[F], y: &[F]) -> F {
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

pub(crate) fn column_shifted<F: Field>(column: &[F]) -> Vec<F> {
    let mut down = unsafe { uninitialized_vec(column.len()) };
    parallel_clone(&column[1..], &mut down[..column.len() - 1]);
    down[column.len() - 1] = column[column.len() - 1];
    down
}
