use p3_field::Field;
use tracing::instrument;
use whir_p3::poly::{evals::eval_eq, multilinear::MultilinearPoint};

/// Evaluates the LDE of the "UP" matrix polynomial.
///
/// This function represents a matrix used to select the "current" row values (e.g., `c[r]`)
/// in AIR constraints.
///
/// ### Behavior
/// The polynomial behaves like an identity matrix for all rows except the last one. To handle
/// the boundary condition of an execution trace, the last row is modified to be a copy of the
/// second-to-last row of the identity matrix.
///
/// ### Example
/// For a trace with `N=4` rows, the matrix represented by this polynomial is:
/// ```text
/// [[1, 0, 0, 0],
///  [0, 1, 0, 0],
///  [0, 0, 1, 0],
///  [0, 0, 1, 0]] <-- The last row is a copy of the row above it from the identity matrix.
/// ```
///
/// ### Arguments
/// * `point`: A slice of `2n` field elements `[s1, s2]`, where:
///   - `s1` is an `n`-element vector representing the **row index**.
///   - `s2` is an `n`-element vector for the **column index**.
///
/// ### Returns
/// A single field element `F` representing the polynomial's evaluation at the given `point`.
pub fn matrix_up_lde<F: Field>(point: &[F]) -> F {
    // Ensure the input point has an even number of variables, so it can be split in half.
    assert!(point.len().is_multiple_of(2));
    // Determine `n`, the number of variables for a single index (row or column).
    let n = point.len() / 2;
    // Split the 2n-element point into two n-element halves: `s1` (column) and `s2` (row).
    let (s1, s2) = point.split_at(n);

    // The polynomial is composed of two main parts:
    // 1. The equality polynomial `eq(s1, s2)`, which evaluates to 1 if the column index
    //    equals the row index, and 0 otherwise. This term constructs the main diagonal
    //    of the identity matrix.
    // 2. A correction term that modifies the matrix based on the input point. This term
    //    is specifically designed to be non-zero only under the conditions that adjust
    //    the last row of the matrix, ensuring the correct boundary behavior.
    MultilinearPoint(s1.to_vec()).eq_poly_outside(&MultilinearPoint(s2.to_vec()))
        + point[..point.len() - 1].iter().copied().product::<F>()
            * (F::ONE - point.last().unwrap().double())
}

/// Evaluates the LDE of the "DOWN" matrix polynomial.
///
/// This function represents a matrix used to select the "next" row values (e.g., `c[r+1]`).
/// It maps row `r` to row `r+1`. For the boundary, it maps the last row to itself.
///
/// ### Behavior
/// The polynomial represents a matrix with `1`s on the superdiagonal (`M[r, r+1] = 1`).
/// For the last row, the entry `M[N-1, N-1]` is also `1` to handle the boundary.
///
/// ### Example
/// For a trace with `N=4` rows, the matrix is:
/// ```text
/// [[0, 1, 0, 0],
///  [0, 0, 1, 0],
///  [0, 0, 0, 1],
///  [0, 0, 0, 1]] // Last row maps to itself.
/// ```
///
/// ### Arguments
/// * `point`: A slice of `2n` field elements `[s1, s2]`, where:
///   - `s1` is an `n`-element vector representing the **row index**.
///   - `s2` is an `n`-element vector for the **column index**.
///
/// ### Returns
/// A single field element `F` representing the polynomial's evaluation at `point`.
pub fn matrix_down_lde<F: Field>(point: &[F]) -> F {
    // The polynomial is the sum of two components:
    // 1. `next_mle(point)`: This polynomial is 1 if `s2` (column index) is the integer
    //    successor of `s1` (row index). This creates the superdiagonal of the matrix.
    next_mle(point)
    // 2. `product(point)`: This is 1 only if all bits in the point are 1. This handles
    //    the bottom-right corner of the matrix, ensuring the last row maps to itself.
    + point.iter().copied().product::<F>()
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
    assert!(
        point.len().is_multiple_of(2),
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

/// Creates the "up" version of a column (`c_up`).
///
/// This corresponds to the `c_up` definition from the paper. It copies the column but
/// replaces the last element with the second-to-last element to handle the boundary case.
///
/// ### Example
/// `[a, b, c, d]` becomes `[a, b, c, c]`
///
/// ### Arguments
/// * `column`: A slice representing a single AIR column.
///
/// ### Returns
/// A new `Vec<F>` with the transformation applied.
pub fn column_up<F: Field>(column: &[F]) -> Vec<F> {
    // Provide a helpful error in debug mode if the column is too short.
    debug_assert!(column.len() >= 2, "column_up requires length >= 2");
    // Create a mutable copy of the input column.
    let mut up = column.to_vec();
    // Overwrite the last element with the value of the second-to-last element.
    up[column.len() - 1] = up[column.len() - 2];
    up
}

/// Creates the "down" version of a column (`c_down`).
///
/// This corresponds to the `c_down` definition from the paper. It shifts the column's elements
/// up by one position and duplicates the new last element to handle the boundary case.
///
/// ### Example
/// `[a, b, c, d]` becomes `[b, c, d, d]`
///
/// ### Arguments
/// * `column`: A slice representing a single AIR column.
///
/// ### Returns
/// A new `Vec<F>` with the transformation applied.
pub fn column_down<F: Field>(column: &[F]) -> Vec<F> {
    // Provide a helpful error in debug mode if the column is empty.
    debug_assert!(
        !column.is_empty(),
        "column_down requires a non-empty column"
    );
    // Get the last element, which will be appended at the end.
    let last_val = column[column.len() - 1];
    // - Create an iterator that skips the first element,
    // - Chains the last element at the end to maintain original length.
    column
        .iter()
        .skip(1)
        .copied()
        .chain(std::iter::once(last_val))
        .collect()
}

/// Computes the folded evaluation vector for the "UP" matrix polynomial.
///
/// This function pre-computes the evaluations of the `matrix_up_lde` polynomial for a
/// fixed set of `outer_challenges` over the entire boolean hypercube of the remaining variables.
///
/// ### Arguments
/// * `outer_challenges`: An `n`-element slice representing the point at which the first
///     `n` variables of the LDE have been fixed.
///
/// ### Returns
/// A `Vec<F>` of size `2^n` containing the evaluations.
#[instrument(name = "matrix_up_folded", skip_all)]
pub fn matrix_up_folded<F: Field>(outer_challenges: &[F]) -> Vec<F> {
    // Get the number of variables, `n`.
    let n = outer_challenges.len();
    // Calculate the size of the evaluation domain (2^n).
    let size = 1 << n;
    // Start with the evaluations of the equality polynomial `eq(X, challenges)`.
    let mut folded = eval_eq(outer_challenges);
    // Calculate the product of all challenges for the correction term.
    let outer_challenges_prod: F = outer_challenges.iter().copied().product();
    // Apply corrections to the last two elements of the evaluation vector.
    folded[size - 1] -= outer_challenges_prod;
    folded[size - 2] += outer_challenges_prod;
    folded
}

/// Computes the folded evaluation vector for the "DOWN" matrix polynomial.
///
/// This function pre-computes the evaluations of the `matrix_down_lde` polynomial for a
/// fixed set of `outer_challenges` over the entire boolean hypercube of the remaining variables.
///
/// ### Behavior
/// The function constructs the evaluation vector by building the underlying polynomial term by term.
/// It iterates through each possible bit position `k`, calculates a corresponding scalar coefficient,
/// and combines it with the evaluations of an equality polynomial over the other variables.
///
/// ### Arguments
/// * `outer_challenges`: An `n`-element slice representing the point at which the first
///     `n` variables of the LDE have been fixed.
///
/// ### Returns
/// A `Vec<F>` of size `2^n` containing the evaluations, which represents one column of the
/// "DOWN" matrix evaluated at the challenge point.
#[instrument(name = "matrix_down_folded", skip_all)]
pub fn matrix_down_folded<F: Field>(outer_challenges: &[F]) -> Vec<F> {
    // Get the number of variables, `n`.
    let n = outer_challenges.len();
    // Calculate the size of the evaluation domain (2^n).
    let size = 1 << n;
    // Initialize the result vector with zeros.
    let mut folded = vec![F::ZERO; size];

    // Precompute products of suffixes of the challenges for efficient lookups.
    // `suffix_prods[i]` will store the product of challenges from index `i` to the end.
    // e.g., for challenges [c0, c1, c2], suffix_prods = [c0*c1*c2, c1*c2, c2, 1]
    let mut suffix_prods = vec![F::ONE; n + 1];
    for i in (0..n).rev() {
        suffix_prods[i] = suffix_prods[i + 1] * outer_challenges[i];
    }

    // This loop constructs the final folded polynomial term by term, iterating through
    // each possible carry position `k` (from right to left).
    for k in 0..n {
        // Calculate the scalar coefficient for this term of the polynomial sum,
        // using the precomputed suffix product for efficiency.
        let scalar = (F::ONE - outer_challenges[n - k - 1]) * suffix_prods[n - k];

        // Get the evaluations of the equality polynomial for the high-order bits.
        let eq_mle = eval_eq(&outer_challenges[0..n - k - 1]);

        // This loop adds the scaled evaluations into the final `folded` vector.
        for (i, &v) in eq_mle.iter().enumerate() {
            // This bit-shifting logic calculates the correct target index in the `folded` vector,
            // which corresponds to constructing the polynomial via tensor products.
            let final_idx = (i << (k + 1)) + (1 << k);
            // The value from the equality polynomial is scaled and added to the target position.
            folded[final_idx] += v * scalar;
        }
    }

    // Add the correction for the bottom-right corner of the matrix, using the
    // precomputed total product of all challenges.
    folded[size - 1] += suffix_prods[0];

    // Return the completed evaluation vector.
    folded
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use p3_koala_bear::KoalaBear;

    use super::*;

    type F = KoalaBear;

    /// Helper function to convert an integer to its big-endian bit representation as field elements.
    /// e.g., `int_to_bits(5, 3)` -> `[F::ONE, F::ZERO, F::ONE]` (for 101_2)
    fn int_to_bits(n: u32, num_bits: usize) -> Vec<F> {
        (0..num_bits)
            .map(|i| {
                if (n >> (num_bits - 1 - i)) & 1 == 1 {
                    F::ONE
                } else {
                    F::ZERO
                }
            })
            .collect()
    }

    #[test]
    #[should_panic]
    fn matrix_up_lde_panics_on_odd_len() {
        // 3 variables is invalid (must be even)
        let _ = matrix_up_lde::<F>(&[F::ZERO, F::ONE, F::ONE]);
    }

    #[test]
    fn test_next_mle_successor_cases() {
        let n = 2; // Testing with 2-bit numbers, so point length is 4.

        // Case: 0 -> 1. x=(0,0), y=(0,1)
        let x = int_to_bits(0, n);
        let y = int_to_bits(1, n);
        assert_eq!(next_mle(&[x, y].concat()), F::ONE, "Failed for 0 -> 1");

        // Case: 1 -> 2. x=(0,1), y=(1,0)
        let x = int_to_bits(1, n);
        let y = int_to_bits(2, n);
        assert_eq!(next_mle(&[x, y].concat()), F::ONE, "Failed for 1 -> 2");

        // Case: 2 -> 3. x=(1,0), y=(1,1)
        let x = int_to_bits(2, n);
        let y = int_to_bits(3, n);
        assert_eq!(next_mle(&[x, y].concat()), F::ONE, "Failed for 2 -> 3");
    }

    #[test]
    fn test_next_mle_non_successor_cases() {
        let n = 2;

        // Case: Not a successor. x=(0,0), y=(1,0) (0 -> 2)
        let x = int_to_bits(0, n);
        let y = int_to_bits(2, n);
        assert_eq!(next_mle(&[x, y].concat()), F::ZERO, "Failed for 0 -> 2");

        // Case: Identity. x=(1,0), y=(1,0) (2 -> 2)
        let x = int_to_bits(2, n);
        let y = int_to_bits(2, n);
        assert_eq!(next_mle(&[x, y].concat()), F::ZERO, "Failed for 2 -> 2");

        // Case: Wrap around (not handled by this function). x=(1,1), y=(0,0) (3 -> 0)
        let x = int_to_bits(3, n);
        let y = int_to_bits(0, n);
        assert_eq!(
            next_mle(&[x, y].concat()),
            F::ZERO,
            "Failed for 3 -> 0 (wrap-around)"
        );
    }

    #[test]
    #[should_panic]
    fn test_matrix_up_lde_panics_on_odd_len() {
        // The function expects an even-length slice (2*n variables),
        let _ = matrix_up_lde::<F>(&[F::ZERO, F::ONE, F::ONE]);
    }

    #[test]
    fn test_matrix_up_lde_on_hypercube() {
        // Set n=2, meaning row and column indices are 2-bit numbers.
        // This corresponds to a 4x4 matrix (2^n x 2^n).
        let n = 2;
        // The matrix M is the identity matrix, except the last row is a copy of the second-to-last
        // row of the identity matrix. M[3] = (0,0,1,0).
        let expected_matrix = [
            // c0 c1 c2 c3
            [F::ONE, F::ZERO, F::ZERO, F::ZERO], // row 0
            [F::ZERO, F::ONE, F::ZERO, F::ZERO], // row 1
            [F::ZERO, F::ZERO, F::ONE, F::ZERO], // row 2
            [F::ZERO, F::ZERO, F::ONE, F::ZERO], // row 3
        ];

        // Iterate through every row index of the 4x4 matrix.
        for r_idx in 0..4 {
            // Iterate through every column index of the 4x4 matrix.
            for c_idx in 0..4 {
                // Convert the integer row index (e.g., 2) into its bit vector ([1, 0]).
                let r_bits = int_to_bits(r_idx, n);
                // Convert the integer column index (e.g., 3) into its bit vector ([1, 1]).
                let c_bits = int_to_bits(c_idx, n);
                // The function's input `point` is the concatenation of the row and column bits.
                let point = [r_bits.as_slice(), c_bits.as_slice()].concat();

                // Get the expected value (0 or 1) from our hardcoded matrix for the current (row, col).
                let expected = expected_matrix[r_idx as usize][c_idx as usize];
                // Call the function with the generated point to get its actual evaluation.
                let actual = matrix_up_lde(&point);

                // Assert that the actual value matches the expected value.
                assert_eq!(actual, expected, "Mismatch at M_up[{r_idx}, {c_idx}]");
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_matrix_down_lde_panics_on_odd_len() {
        // The function expects an even-length slice (2*n variables).
        let _ = matrix_down_lde::<F>(&[F::ZERO, F::ONE, F::ONE]);
    }

    #[test]
    fn test_matrix_down_lde_on_hypercube() {
        // Set n=2 for a 4x4 matrix.
        let n = 2;
        // The matrix M has 1s on the superdiagonal (col = row + 1)
        // and the last two rows are identical (0,0,0,1).
        let expected_matrix = [
            // c0 c1 c2 c3
            [F::ZERO, F::ONE, F::ZERO, F::ZERO], // row 0
            [F::ZERO, F::ZERO, F::ONE, F::ZERO], // row 1
            [F::ZERO, F::ZERO, F::ZERO, F::ONE], // row 2
            [F::ZERO, F::ZERO, F::ZERO, F::ONE], // row 3
        ];

        // Iterate through every row index of the 4x4 matrix.
        for r_idx in 0..4 {
            // Iterate through every column index of the 4x4 matrix.
            for c_idx in 0..4 {
                // Convert the integer row index to its bit vector.
                let r_bits = int_to_bits(r_idx, n);
                // Convert the integer column index to its bit vector.
                let c_bits = int_to_bits(c_idx, n);
                // Concatenate bits to form the function's input point.
                let point = [r_bits.as_slice(), c_bits.as_slice()].concat();

                // Get the expected value from our hardcoded matrix.
                let expected = expected_matrix[r_idx as usize][c_idx as usize];
                // Call the function to get the actual evaluated value.
                let actual = matrix_down_lde(&point);

                // Assert that the actual value matches the expected value from the matrix.
                assert_eq!(actual, expected, "Mismatch at M_down[{r_idx}, {c_idx}]");
            }
        }
    }

    #[test]
    fn test_column_up() {
        // Create a sample column vector with four distinct field elements.
        let col = vec![
            F::from_u32(10),
            F::from_u32(20),
            F::from_u32(30),
            F::from_u32(40),
        ];

        // The `column_up` function duplicates the second-to-last element into the last position.
        //
        // Transformation logic:
        //
        // [10]        [10]
        // [20]        [20]
        // [30]  --->  [30]
        // [40]        [30]  <-- This value is copied from the one above.
        //
        let expected = vec![
            F::from_u32(10),
            F::from_u32(20),
            F::from_u32(30),
            F::from_u32(30),
        ];
        // Assert that the function produces the correct "up" column.
        assert_eq!(column_up(&col), expected);

        // Test the edge case with a column of length 2.
        let col_len2 = vec![F::from_u32(5), F::from_u32(8)];
        //
        // Transformation logic for length 2:
        //
        // [5]   --->  [5]
        // [8]         [5]  <-- Copied from above.
        //
        let expected_len2 = vec![F::from_u32(5), F::from_u32(5)];
        assert_eq!(column_up(&col_len2), expected_len2);
    }

    #[test]
    #[should_panic]
    fn test_column_up_panics_on_len_1() {
        column_up(&[F::ONE]);
    }

    #[test]
    fn test_column_down() {
        // Create a sample column vector.
        let col = vec![
            F::from_u32(10),
            F::from_u32(20),
            F::from_u32(30),
            F::from_u32(40),
        ];

        // The `column_down` function shifts all elements up by one position
        // and then duplicates the new last element to maintain the original length.
        //
        // Transformation logic:
        //
        // [10]        [20]  <-- Shifted up
        // [20]        [30]  <-- Shifted up
        // [30]  --->  [40]  <-- Shifted up
        // [40]        [40]  <-- Duplicated from the new last element above
        //
        let expected = vec![
            F::from_u32(20),
            F::from_u32(30),
            F::from_u32(40),
            F::from_u32(40),
        ];
        // Assert that the function produces the correct "down" column.
        assert_eq!(column_down(&col), expected);

        // Test the edge case with a column of length 2.
        let col_len2 = vec![F::from_u32(5), F::from_u32(8)];
        //
        // Transformation logic for length 2:
        //
        // [5]   --->  [8]
        // [8]         [8]  <-- Duplicated
        //
        let expected_len2 = vec![F::from_u32(8), F::from_u32(8)];
        assert_eq!(column_down(&col_len2), expected_len2);
    }

    #[test]
    fn test_matrix_up_folded_vs_lde() {
        // Set n=3 variables, meaning we are testing the logic on an 8x8 matrix (since 2^3 = 8).
        let n = 3;
        // Calculate the number of rows/columns, which is 8.
        let num_coords = 1 << n;

        // This test verifies that `matrix_up_folded` is consistent with `matrix_up_lde`.
        // We iterate through each column of the matrix.
        for c_idx in 0..num_coords {
            // Convert the integer column index (e.g., 6) into its bit representation (e.g., [1, 1, 0]).
            let c_bits = int_to_bits(c_idx as u32, n);
            // Call `matrix_up_folded` to get the evaluations for the entire column `c_idx`.
            //
            // This vector represents the polynomial M(X, c_bits) evaluated for all boolean X.
            let folded_col = matrix_up_folded(&c_bits);
            // Sanity check: the resulting vector should have 8 elements, one for each row.
            assert_eq!(folded_col.len(), num_coords as usize);

            // Now, for the fixed column, we check each row's value.
            for r_idx in 0..num_coords {
                // Convert the integer row index (e.g., 7) into its bit representation (e.g., [1, 1, 1]).
                let r_bits = int_to_bits(r_idx as u32, n);

                // We construct the input point for the LDE by concatenating:
                // - the COLUMN bits first,
                // - then the ROW bits.
                // This aligns the test's variable ordering with the one implicitly used by the `folded` functions.
                let point = [c_bits.as_slice(), r_bits.as_slice()].concat();

                // Evaluate the `lde` function at this specific point to get the "ground truth" value.
                let lde_val = matrix_up_lde(&point);
                // Get the corresponding value from the pre-calculated `folded_col` vector.
                let folded_val = folded_col[r_idx as usize];

                // Assert that the value from the folded evaluation matches the direct LDE evaluation.
                //
                // This confirms that both functions represent the same underlying polynomial.
                assert_eq!(
                    lde_val, folded_val,
                    "Mismatch for M_up(col={c_idx}, row={r_idx})"
                );
            }
        }
    }

    #[test]
    fn test_matrix_down_folded_vs_lde() {
        // Set n=3 variables for an 8x8 matrix.
        let n = 3;
        // Calculate the number of rows/columns.
        let num_coords = 1 << n;

        // We iterate through each column to verify the consistency between the `folded` and `lde` functions.
        for c_idx in 0..num_coords {
            // Convert the column index to its bit representation.
            let c_bits = int_to_bits(c_idx as u32, n);
            // Get the entire column's evaluations from the `folded` function.
            let folded_col = matrix_down_folded(&c_bits);
            // Check if the output vector has the correct number of row entries.
            assert_eq!(folded_col.len(), num_coords as usize);

            // For the given column, check each row's value.
            for r_idx in 0..num_coords {
                // Convert the row index to its bit representation.
                let r_bits = int_to_bits(r_idx as u32, n);

                // We construct the input point for the LDE by concatenating:
                // - the COLUMN bits first,
                // - then the ROW bits.
                // This aligns the test's variable ordering with the one implicitly used by the `folded` functions.
                let point = [c_bits.as_slice(), r_bits.as_slice()].concat();

                // Calculate the expected value by calling the `lde` function directly.
                let lde_val = matrix_down_lde(&point);
                // Get the actual value from the `folded` function's result vector.
                let folded_val = folded_col[r_idx as usize];

                // Assert that the two values are identical.
                assert_eq!(
                    lde_val, folded_val,
                    "Mismatch for M_down(col={c_idx}, row={r_idx})"
                );
            }
        }
    }
}
