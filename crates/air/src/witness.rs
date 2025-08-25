// TODO use RowMajorMatrix

use std::{
    borrow::Borrow,
    ops::{Deref, Range},
};

use p3_field::Field;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use rayon::prelude::*;

use crate::utils::{column_down, column_up};

/// A non-owning view of an AIR witness, organized by columns.
#[derive(Debug)]
pub struct AirWitness<'a, F> {
    /// A vector of slices, where each slice represents a full column of the witness trace.
    pub cols: Vec<&'a [F]>,
    /// Defines contiguous groups of columns, providing structure to the witness.
    pub column_groups: &'a [Range<usize>],
}

impl<'a, F> Deref for AirWitness<'a, F> {
    type Target = [&'a [F]];
    fn deref(&self) -> &Self::Target {
        &self.cols
    }
}

impl<'a, F> AirWitness<'a, F> {
    /// Creates a new witness view from column data and group definitions.
    pub fn new(cols: &'a [impl Borrow<[F]>], column_groups: &'a [Range<usize>]) -> Self {
        // Create a column view from the borrowed slices.
        let cols = cols.iter().map(Borrow::borrow).collect::<Vec<_>>();

        // Input Validation

        // Handle the edge case of an empty witness first.
        if cols.is_empty() {
            assert!(
                column_groups.is_empty(),
                "Cannot have column groups for an empty witness"
            );
            return Self {
                cols,
                column_groups,
            };
        }

        // For a non-empty witness, perform all necessary checks.
        let n_rows = cols[0].len();
        // Check that the number of rows is a power of two.
        assert!(
            n_rows.is_power_of_two(),
            "Number of rows must be a power of two"
        );
        // Check that all columns have the same number of rows.
        assert!(
            cols.iter().all(|c| c.len() == n_rows),
            "All columns must have the same length"
        );

        // Ensure there is at least one column group for a non-empty witness.
        assert!(
            !column_groups.is_empty(),
            "Must have at least one column group"
        );

        // Validate the structure of the column groups.
        assert_eq!(
            column_groups.first().unwrap().start,
            0,
            "Column groups must start at index 0"
        );
        assert_eq!(
            column_groups.last().unwrap().end,
            cols.len(),
            "Column groups must end at the last column index"
        );
        assert!(
            column_groups.windows(2).all(|w| w[0].end == w[1].start),
            "Column groups must be contiguous"
        );
        assert!(
            column_groups.iter().all(|r| !r.is_empty()),
            "Column groups cannot be empty"
        );

        Self {
            cols,
            column_groups,
        }
    }

    /// Returns the total number of columns in the witness.
    #[must_use]
    pub const fn n_columns(&self) -> usize {
        self.cols.len()
    }

    /// Returns the number of rows in the witness trace.
    #[must_use]
    pub fn n_rows(&self) -> usize {
        self.cols[0].len()
    }

    /// Returns the base-2 logarithm of the number of rows.
    #[must_use]
    pub fn log_n_rows(&self) -> usize {
        log2_strict_usize(self.n_rows())
    }

    /// Returns the size of the largest column group.
    #[must_use]
    pub fn max_columns_per_group(&self) -> usize {
        self.column_groups.iter().map(Range::len).max().unwrap()
    }

    /// Returns the smallest power of two >= the size of the largest column group.
    #[must_use]
    pub fn log_max_columns_per_group(&self) -> usize {
        log2_ceil_usize(self.max_columns_per_group())
    }
}

impl<F> AirWitness<'_, F>
where
    F: Field + Send + Sync,
{
    /// Generates the "up" and "down" shifted columns for the entire witness.
    ///
    /// This method efficiently creates the `c_up` and `c_down` columns required by the AIR
    /// zerocheck protocol. It operates in parallel on the witness columns.
    ///
    /// ### Returns
    /// A `Vec` of owned columns `Vec<Vec<F>>` in the order `[up(c0), ..., up(cn), down(c0), ..., down(cn)]`.
    #[must_use]
    pub fn shifted_columns(&self) -> Vec<Vec<F>> {
        // Process "up" columns.
        let up_cols = self.cols.par_iter().map(|c| column_up(c));
        // Process "down" columns.
        let down_cols = self.cols.par_iter().map(|c| column_down(c));
        // Chain the two iterators and collect the results into a single vector.
        up_cols.chain(down_cols).collect()
    }
}

#[cfg(test)]
#[allow(clippy::single_range_in_vec_init)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use p3_koala_bear::KoalaBear;

    use super::*;

    type F = KoalaBear;

    /// A helper to create simple column data for tests.
    fn get_test_cols() -> (Vec<F>, Vec<F>) {
        let col1 = vec![
            F::from_u32(1),
            F::from_u32(2),
            F::from_u32(3),
            F::from_u32(4),
        ];
        let col2 = vec![
            F::from_u32(5),
            F::from_u32(6),
            F::from_u32(7),
            F::from_u32(8),
        ];
        (col1, col2)
    }

    #[test]
    fn test_shifted_columns() {
        // Create two sample columns to process.
        // Note: The number of rows must be a power of two for AirWitness::new to succeed.
        let col1 = vec![
            F::from_u32(1),
            F::from_u32(2),
            F::from_u32(3),
            F::from_u32(4),
        ];
        let col2 = vec![
            F::from_u32(5),
            F::from_u32(6),
            F::from_u32(7),
            F::from_u32(8),
        ];

        // Create an AirWitness instance to test the `shifted_columns` method.
        // The column_groups can be a single group covering all columns for this test.
        let cols = vec![col1.as_slice(), col2.as_slice()];
        let witness = AirWitness::new(&cols, &[0..2]);

        // The method first applies `column_up` to all witness columns,
        // then applies `column_down` to all columns, and finally
        // collects the results in that order.
        //
        // Input Columns (in witness):
        // col1 | col2
        // -----|-----
        //   1  |  5
        //   2  |  6
        //   3  |  7
        //   4  |  8
        //
        // Expected Output Structure:
        // [ up(col1), up(col2), down(col1), down(col2) ]
        //
        // up(col1)   = [1, 2, 3, 3]
        // up(col2)   = [5, 6, 7, 7]
        // down(col1) = [2, 3, 4, 4]
        // down(col2) = [6, 7, 8, 8]
        let expected = vec![
            vec![
                F::from_u32(1),
                F::from_u32(2),
                F::from_u32(3),
                F::from_u32(3),
            ], // up(col1)
            vec![
                F::from_u32(5),
                F::from_u32(6),
                F::from_u32(7),
                F::from_u32(7),
            ], // up(col2)
            vec![
                F::from_u32(2),
                F::from_u32(3),
                F::from_u32(4),
                F::from_u32(4),
            ], // down(col1)
            vec![
                F::from_u32(6),
                F::from_u32(7),
                F::from_u32(8),
                F::from_u32(8),
            ], // down(col2)
        ];

        // Assert that the method correctly processes and collects all results.
        assert_eq!(witness.shifted_columns(), expected);
    }

    #[test]
    fn test_new_success() {
        // Arrange: Create valid columns and column groups.
        let (col1, col2) = get_test_cols();
        let cols = vec![col1.as_slice(), col2.as_slice()];

        // Scenario 1: Single column group.
        let groups_single = [0..2];
        let witness_single = AirWitness::new(&cols, &groups_single);
        assert_eq!(witness_single.cols.len(), 2);
        assert_eq!(witness_single.column_groups.len(), 1);

        // Scenario 2: Multiple contiguous column groups.
        let groups_multi = [0..1, 1..2];
        let witness_multi = AirWitness::new(&cols, &groups_multi);
        assert_eq!(witness_multi.cols.len(), 2);
        assert_eq!(witness_multi.column_groups.len(), 2);

        // Scenario 3: Empty witness.
        let cols_empty: Vec<&[F]> = Vec::new();
        let groups_empty = [];
        let witness_empty = AirWitness::new(&cols_empty, &groups_empty);
        assert!(witness_empty.cols.is_empty());
        assert!(witness_empty.column_groups.is_empty());
    }

    #[test]
    #[should_panic]
    fn test_new_panics_on_non_power_of_two_rows() {
        // Arrange: Create a column with 3 rows, which is not a power of two.
        let col1 = vec![F::from_u32(1), F::from_u32(2), F::from_u32(3)];
        let cols = vec![col1.as_slice()];
        // Act & Assert: This should panic.
        AirWitness::new(&cols, &[0..1]);
    }

    #[test]
    #[should_panic]
    fn test_new_panics_on_unequal_column_lengths() {
        // Arrange: Create two columns with different lengths.
        let col1 = vec![F::from_u32(1), F::from_u32(2)];
        let col2 = vec![
            F::from_u32(1),
            F::from_u32(2),
            F::from_u32(3),
            F::from_u32(4),
        ];
        let cols = vec![col1.as_slice(), col2.as_slice()];
        // Act & Assert: This should panic.
        AirWitness::new(&cols, &[0..2]);
    }

    #[test]
    #[should_panic]
    fn test_new_panics_on_group_not_starting_at_zero() {
        let (col1, col2) = get_test_cols();
        let cols = vec![col1.as_slice(), col2.as_slice()];
        // Arrange: Groups start at 1 instead of 0.
        AirWitness::new(&cols, &[1..2]);
    }

    #[test]
    #[should_panic]
    fn test_new_panics_on_group_not_ending_at_len() {
        let (col1, col2) = get_test_cols();
        let cols = vec![col1.as_slice(), col2.as_slice()];
        // Arrange: The last group ends at 1, but there are 2 columns.
        AirWitness::new(&cols, &[0..1]);
    }

    #[test]
    #[should_panic]
    fn test_new_panics_on_non_contiguous_groups() {
        let (col1, col2) = get_test_cols();
        let cols = vec![col1.as_slice(), col2.as_slice(), col1.as_slice()];
        // Arrange: There is a gap between the end of the first group (1) and the start of the second (2).
        AirWitness::new(&cols, &[0..1, 2..3]);
    }

    #[test]
    #[should_panic]
    fn test_new_panics_on_empty_group() {
        let (col1, col2) = get_test_cols();
        let cols = vec![col1.as_slice(), col2.as_slice()];
        // Arrange: The second group `1..1` is empty.
        AirWitness::new(&cols, &[0..1, 1..1, 1..2]);
    }

    #[test]
    fn test_accessors_and_deref() {
        // Arrange: Create a standard witness.
        let (col1, col2) = get_test_cols();
        let cols = vec![col1.as_slice(), col2.as_slice()];
        let witness = AirWitness::new(&cols, &[0..1, 1..2]);

        // Act & Assert: Test all accessor methods.
        assert_eq!(witness.n_columns(), 2);
        assert_eq!(witness.n_rows(), 4);
        assert_eq!(witness.log_n_rows(), 2);
        assert_eq!(witness.max_columns_per_group(), 1);
        assert_eq!(witness.log_max_columns_per_group(), 0); // log2_ceil(1) = 0

        // Test Deref by using slice methods directly on the witness.
        assert_eq!(witness.len(), 2);
        assert_eq!(witness[0], col1.as_slice());
        assert_eq!(witness[1], col2.as_slice());
    }

    #[test]
    fn test_shifted_columns_edge_cases() {
        // Scenario 1: Witness with a single column.
        let col1 = vec![F::ONE, F::TWO];
        let cols = [col1.as_slice()];
        let witness_one_col = AirWitness::new(&cols, &[0..1]);
        let expected_one_col = vec![
            vec![F::ONE, F::ONE], // up(col1)
            vec![F::TWO, F::TWO], // down(col1)
        ];
        assert_eq!(witness_one_col.shifted_columns(), expected_one_col);

        // Scenario 2: Witness with no columns.
        let cols_empty: Vec<&[F]> = Vec::new();
        let groups_empty = [];
        let witness_empty = AirWitness::new(&cols_empty, &groups_empty);
        let expected_empty: Vec<Vec<F>> = vec![];
        assert_eq!(witness_empty.shifted_columns(), expected_empty);
    }
}
