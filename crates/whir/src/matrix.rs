// Credits: whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).

use std::{
    borrow::{Borrow, BorrowMut},
    iter,
    marker::PhantomData,
    ops::Deref,
};

use field::{ExtensionField, Field, PackedValue};
use itertools::Itertools;

pub trait Matrix<T: Send + Sync + Clone>: Send + Sync {
    fn width(&self) -> usize;
    fn height(&self) -> usize;

    fn dimensions(&self) -> Dimensions {
        Dimensions {
            width: self.width(),
            height: self.height(),
        }
    }

    #[inline]
    fn row(&self, r: usize) -> Option<impl IntoIterator<Item = T, IntoIter = impl Iterator<Item = T> + Send + Sync>> {
        (r < self.height()).then(|| unsafe { self.row_unchecked(r) })
    }

    /// # Safety
    /// The caller must ensure that `r < self.height()`.
    #[inline]
    unsafe fn row_unchecked(
        &self,
        r: usize,
    ) -> impl IntoIterator<Item = T, IntoIter = impl Iterator<Item = T> + Send + Sync> {
        unsafe { self.row_subseq_unchecked(r, 0, self.width()) }
    }

    /// # Safety
    /// The caller must ensure that `r < self.height()` and `start <= end <= self.width()`.
    #[inline]
    unsafe fn row_subseq_unchecked(
        &self,
        r: usize,
        start: usize,
        end: usize,
    ) -> impl IntoIterator<Item = T, IntoIter = impl Iterator<Item = T> + Send + Sync> {
        unsafe { self.row_unchecked(r).into_iter().skip(start).take(end - start) }
    }

    /// # Safety
    /// The caller must ensure that `r < self.height()`.
    #[inline]
    unsafe fn row_slice_unchecked(&self, r: usize) -> impl Deref<Target = [T]> {
        unsafe { self.row_subslice_unchecked(r, 0, self.width()) }
    }

    /// # Safety
    /// The caller must ensure that `r < self.height()` and `start <= end <= self.width()`.
    #[inline]
    unsafe fn row_subslice_unchecked(&self, r: usize, start: usize, end: usize) -> impl Deref<Target = [T]> {
        unsafe { self.row_subseq_unchecked(r, start, end).into_iter().collect_vec() }
    }

    #[inline]
    fn rows(&self) -> impl Iterator<Item = impl Iterator<Item = T>> + Send + Sync {
        unsafe { (0..self.height()).map(move |r| self.row_unchecked(r).into_iter()) }
    }

    fn wrapping_row_slices(&self, r: usize, c: usize) -> Vec<impl Deref<Target = [T]>> {
        unsafe {
            (0..c)
                .map(|i| self.row_slice_unchecked((r + i) % self.height()))
                .collect_vec()
        }
    }

    fn to_row_major_matrix(self) -> RowMajorMatrix<T>
    where
        Self: Sized,
        T: Clone,
    {
        RowMajorMatrix::new(self.rows().flatten().collect(), self.width())
    }

    // #[inline]
    // fn vertically_packed_row<P>(&self, r: usize) -> impl Iterator<Item = P>
    // where
    //     T: Copy,
    //     P: PackedValue<Value = T>,
    // {
    //     let rows = self.wrapping_row_slices(r, P::WIDTH);
    //     (0..self.width()).map(move |c| P::from_fn(|i| rows[i][c]))
    // }

    #[inline]
    fn vertically_packed_row_rtl<P>(
        &self,
        r: usize,
        effective_width: usize,
        n_leading_zeros: usize,
    ) -> impl Iterator<Item = P>
    where
        T: Copy,
        P: PackedValue<Value = T> + Default,
    {
        let rows = self.wrapping_row_slices(r, P::WIDTH);
        (0..n_leading_zeros)
            .map(|_| P::default())
            .chain((0..effective_width).rev().map(move |c| P::from_fn(|i| rows[i][c])))
    }
}

pub(crate) type RowMajorMatrix<T> = DenseMatrix<T>;
pub type RowMajorMatrixViewMut<'a, T> = DenseMatrix<T, &'a mut [T]>;

impl<T: Clone + Send + Sync, S: DenseStorage<T>> DenseMatrix<T, S> {
    pub fn as_view_mut(&mut self) -> RowMajorMatrixViewMut<'_, T>
    where
        S: BorrowMut<[T]>,
    {
        RowMajorMatrixViewMut::new(self.values.borrow_mut(), self.width)
    }
}

#[derive(Debug, Clone)]
pub struct FlatMatrixView<F, EF, Inner>(Inner, PhantomData<(F, EF)>);

impl<F, EF, Inner> FlatMatrixView<F, EF, Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self(inner, PhantomData)
    }
}

impl<F, EF, Inner> Deref for FlatMatrixView<F, EF, Inner> {
    type Target = Inner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F, EF, Inner> Matrix<F> for FlatMatrixView<F, EF, Inner>
where
    F: Field,
    EF: ExtensionField<F>,
    Inner: Matrix<EF>,
{
    fn width(&self) -> usize {
        self.0.width() * EF::DIMENSION
    }

    fn height(&self) -> usize {
        self.0.height()
    }

    unsafe fn row_subseq_unchecked(
        &self,
        r: usize,
        start: usize,
        end: usize,
    ) -> impl IntoIterator<Item = F, IntoIter = impl Iterator<Item = F> + Send + Sync> {
        // We can skip the first start / EF::DIMENSION elements in the row.
        let len = end - start;
        let inner_start = start / EF::DIMENSION;
        unsafe {
            // Safety: The caller must ensure that r < self.height(), start <= end and end < self.width().
            FlatIter {
                inner: self
                    .0
                    // We set end to be the width of the inner matrix and use take to ensure we get the right
                    // number of elements.
                    .row_subseq_unchecked(r, inner_start, self.0.width())
                    .into_iter()
                    .peekable(),
                idx: start,
                _phantom: PhantomData,
            }
            .take(len)
        }
    }
}

pub struct FlatIter<F, I: Iterator> {
    inner: iter::Peekable<I>,
    idx: usize,
    _phantom: PhantomData<F>,
}

impl<F, EF, I> Iterator for FlatIter<F, I>
where
    F: Field,
    EF: ExtensionField<F>,
    I: Iterator<Item = EF>,
{
    type Item = F;
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == EF::DIMENSION {
            self.idx = 0;
            self.inner.next();
        }
        let value = self.inner.peek()?.as_basis_coefficients_slice()[self.idx];
        self.idx += 1;
        Some(value)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Dimensions {
    /// Number of columns in the matrix.
    pub width: usize,
    /// Number of rows in the matrix.
    pub height: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DenseMatrix<T, V = Vec<T>> {
    /// Flat buffer of matrix values in row-major order.
    pub values: V,
    /// Number of columns in the matrix.
    ///
    /// The number of rows is implicitly determined as `values.len() / width`.
    pub width: usize,
    /// Marker for the element type `T`, unused directly.
    ///
    /// Required to retain type information when `V` does not own or contain `T`.
    _phantom: PhantomData<T>,
}

impl<T: Clone + Send + Sync, S: DenseStorage<T>> DenseMatrix<T, S> {
    /// Create a new dense matrix of the given dimensions, backed by the given storage.
    ///
    /// Note that it is undefined behavior to create a matrix such that
    /// `values.len() % width != 0`.
    #[must_use]
    pub fn new(values: S, width: usize) -> Self {
        debug_assert!(values.borrow().len().is_multiple_of(width));
        Self {
            values,
            width,
            _phantom: PhantomData,
        }
    }
}

impl<T: Clone + Send + Sync, S: DenseStorage<T>> Matrix<T> for DenseMatrix<T, S> {
    #[inline]
    fn width(&self) -> usize {
        self.width
    }

    #[inline]
    fn height(&self) -> usize {
        self.values.borrow().len().checked_div(self.width).unwrap_or(0)
    }

    #[inline]
    unsafe fn row_subseq_unchecked(
        &self,
        r: usize,
        start: usize,
        end: usize,
    ) -> impl IntoIterator<Item = T, IntoIter = impl Iterator<Item = T> + Send + Sync> {
        unsafe {
            // Safety: The caller must ensure that r < self.height() and start <= end <= self.width().
            self.values
                .borrow()
                .get_unchecked(r * self.width + start..r * self.width + end)
                .iter()
                .cloned()
        }
    }

    #[inline]
    unsafe fn row_subslice_unchecked(&self, r: usize, start: usize, end: usize) -> impl Deref<Target = [T]> {
        unsafe {
            self.values
                .borrow()
                .get_unchecked(r * self.width + start..r * self.width + end)
        }
    }

    fn to_row_major_matrix(self) -> RowMajorMatrix<T>
    where
        Self: Sized,
        T: Clone,
    {
        RowMajorMatrix::new(self.values.to_vec(), self.width)
    }
}

pub trait DenseStorage<T>: Borrow<[T]> + Send + Sync {
    fn to_vec(self) -> Vec<T>;
}

// Cow doesn't impl IntoOwned so we can't blanket it
impl<T: Clone + Send + Sync> DenseStorage<T> for Vec<T> {
    fn to_vec(self) -> Self {
        self
    }
}

impl<T: Clone + Send + Sync> DenseStorage<T> for &[T] {
    fn to_vec(self) -> Vec<T> {
        <[T]>::to_vec(self)
    }
}

impl<T: Clone + Send + Sync> DenseStorage<T> for &mut [T] {
    fn to_vec(self) -> Vec<T> {
        <[T]>::to_vec(self)
    }
}
