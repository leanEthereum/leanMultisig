use p3_field::Field;
use rayon::prelude::*;
use whir_p3::poly::multilinear::MultilinearPoint;

pub(crate) fn matrix_up_lde<F: Field>(point: &[F]) -> F {
    /*
        Matrix UP:

       (1 0 0 0 ... 0 0 0)
       (0 1 0 0 ... 0 0 0)
       (0 0 1 0 ... 0 0 0)
       (0 0 0 1 ... 0 0 0)
       ...      ...   ...
       (0 0 0 0 ... 1 0 0)
       (0 0 0 0 ... 0 1 0)
       (0 0 0 0 ... 0 1 0)

       Square matrix of size self.n_columns x sef.n_columns
       As a multilinear polynomial in 2 * log_length variables:
       - self.n_columns first variables -> encoding the row index
       - self.n_columns last variables -> encoding the column index
    */

    assert_eq!(point.len() % 2, 0);
    let n = point.len() / 2;
    let (s1, s2) = point.split_at(n);
    MultilinearPoint(s1.to_vec()).eq_poly_outside(&MultilinearPoint(s2.to_vec()))
        + point[..point.len() - 1].iter().copied().product::<F>()
            * (F::ONE - point[point.len() - 1] * F::TWO)
}

pub(crate) fn matrix_down_lde<F: Field>(point: &[F]) -> F {
    /*
        Matrix DOWN:

       (0 1 0 0 ... 0 0 0)
       (0 0 1 0 ... 0 0 0)
       (0 0 0 1 ... 0 0 0)
       (0 0 0 0 ... 0 0 0)
       (0 0 0 0 ... 0 0 0)
       ...      ...   ...
       (0 0 0 0 ... 0 1 0)
       (0 0 0 0 ... 0 0 1)
       (0 0 0 0 ... 0 0 1)

       Square matrix of size self.n_columns x sef.n_columns
       As a multilinear polynomial in 2 * log_length variables:
       - self.n_columns first variables -> encoding the row index
       - self.n_columns last variables -> encoding the column index

       TODO OPTIMIZATIOn:
       the lde currently is in log(table_length)^2, but it could be log(table_length) using a recursive construction
       (However it is not representable as a polynomial in this case, but as a fraction instead)

    */
    next_mle(point) + point.iter().copied().product::<F>()

    // bottom right corner
}

/// Returns a multilinear polynomial in 2n variables that evaluates to 1
/// if and only if the second n-bit vector is equal to the first vector plus one (viewed as big-endian integers).
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
fn next_mle<F: Field>(point: &[F]) -> F {
    // Check that the point length is even: we split into x and y of equal length.
    assert_eq!(
        point.len() % 2,
        0,
        "Input point must have an even number of variables."
    );
    let n = point.len() / 2;

    // Split point into x (first n) and y (last n).
    let (x, y) = point.split_at(n);

    // Sum contributions for each possible carry position k = 0..n-1.
    (0..n)
        .map(|k| {
            // Term 1: bits to the left of k match
            //
            // For i > k, enforce x_i == y_i.
            // Using equality polynomial: x_i * y_i + (1 - x_i)*(1 - y_i).
            //
            // Indices are reversed because bits are big-endian.
            let eq_high_bits = (k + 1..n)
                .map(|i| {
                    x[n - 1 - i] * y[n - 1 - i] + (F::ONE - x[n - 1 - i]) * (F::ONE - y[n - 1 - i])
                })
                .product::<F>();

            // Term 2: carry bit at position k
            //
            // Enforce x_k = 0 and y_k = 1.
            // Condition: (1 - x_k) * y_k.
            let carry_bit = (F::ONE - x[n - 1 - k]) * y[n - 1 - k];

            // Term 3: bits to the right of k are 1 in x and 0 in y
            //
            // For i < k, enforce x_i = 1 and y_i = 0.
            // Condition: x_i * (1 - y_i).
            let low_bits_are_one_zero = (0..k)
                .map(|i| x[n - 1 - i] * (F::ONE - y[n - 1 - i]))
                .product::<F>();

            // Multiply the three terms for this k, representing one "carry pattern".
            eq_high_bits * carry_bit * low_bits_are_one_zero
        })
        // Sum over all carry positions: any valid "k" gives contribution 1.
        .sum()
}

pub(crate) fn columns_up_and_down<F: Field>(columns: &[&[F]]) -> Vec<Vec<F>> {
    columns
        .par_iter()
        .map(|c| column_up(c))
        .chain(columns.par_iter().map(|c| column_down(c)))
        .collect()
}

pub(crate) fn column_up<F: Field>(column: &[F]) -> Vec<F> {
    let mut up = column.to_vec();
    up[column.len() - 1] = up[column.len() - 2];
    up
}

pub(crate) fn column_down<F: Field>(column: &[F]) -> Vec<F> {
    let mut down = column[1..].to_vec();
    down.push(*down.last().unwrap());
    down
}
