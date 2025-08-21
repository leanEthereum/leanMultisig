// TODO use RowMajorMatrix

use std::{
    borrow::Borrow,
    ops::{Deref, Range},
};

use p3_util::{log2_ceil_usize, log2_strict_usize};

#[derive(Debug)]
pub struct AirWitness<'a, F> {
    pub cols: Vec<&'a [F]>,
    pub column_groups: Vec<Range<usize>>,
}

impl<'a, F> Deref for AirWitness<'a, F> {
    type Target = [&'a [F]];
    fn deref(&self) -> &Self::Target {
        &self.cols
    }
}

impl<'a, F> AirWitness<'a, F> {
    pub fn new(cols: &'a [impl Borrow<[F]>], column_groups: &[Range<usize>]) -> Self {
        let cols = cols.iter().map(|col| col.borrow()).collect::<Vec<_>>();
        assert!(
            cols.iter()
                .all(|col| col.len() == (1 << log2_strict_usize(cols[0].len()))),
        );
        assert!(column_groups[0].start == 0);
        assert!(column_groups.last().unwrap().end == cols.len());
        assert!(column_groups.windows(2).all(|w| w[0].end == w[1].start));
        assert!(column_groups.iter().all(|r| r.start < r.end));
        Self {
            cols,
            column_groups: column_groups.to_vec(),
        }
    }

    pub fn n_columns(&self) -> usize {
        self.cols.len()
    }

    pub fn n_rows(&self) -> usize {
        self.cols[0].len()
    }

    pub fn log_n_rows(&self) -> usize {
        log2_strict_usize(self.n_rows())
    }

    pub fn max_columns_per_group(&self) -> usize {
        self.column_groups.iter().map(|g| g.len()).max().unwrap()
    }

    pub fn log_max_columns_per_group(&self) -> usize {
        log2_ceil_usize(self.max_columns_per_group())
    }
}
