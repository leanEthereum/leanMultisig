use std::sync::atomic::{AtomicPtr, Ordering};

use multilinear_toolkit::prelude::*;

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

pub fn transpose_slice_to_basis_coefficients<F: Field, EF: ExtensionField<F>>(slice: &[EF]) -> Vec<Vec<F>> {
    let res = vec![F::zero_vec(slice.len()); EF::DIMENSION];
    slice.par_iter().enumerate().for_each(|(i, row)| {
        let coeffs = EF::as_basis_coefficients_slice(row);
        unsafe {
            for (j, &coeff) in coeffs.iter().enumerate() {
                let raw_ptr = res[j].as_ptr() as *mut F;
                *raw_ptr.add(i) = coeff;
            }
        }
    });
    res
}

pub fn dot_product_with_base<EF: ExtensionField<PF<EF>>>(slice: &[EF]) -> EF {
    assert_eq!(slice.len(), <EF as BasedVectorSpace<PF<EF>>>::DIMENSION);
    (0..EF::DIMENSION)
        .map(|i| slice[i] * <EF as BasedVectorSpace<PF<EF>>>::ith_basis_element(i).unwrap())
        .sum::<EF>()
}

pub fn to_big_endian_bits(value: usize, bit_count: usize) -> Vec<bool> {
    (0..bit_count).rev().map(|i| (value >> i) & 1 == 1).collect()
}

pub fn to_big_endian_in_field<F: Field>(value: usize, bit_count: usize) -> Vec<F> {
    (0..bit_count)
        .rev()
        .map(|i| F::from_bool((value >> i) & 1 == 1))
        .collect()
}

pub fn to_little_endian_bits(value: usize, bit_count: usize) -> Vec<bool> {
    let mut res = to_big_endian_bits(value, bit_count);
    res.reverse();
    res
}

pub fn to_little_endian_in_field<F: Field>(value: usize, bit_count: usize) -> Vec<F> {
    let mut res = to_big_endian_in_field::<F>(value, bit_count);
    res.reverse();
    res
}

/// Reverses the order of the lowest `n_bits` bits of `x`.
pub fn bit_reverse(x: usize, n_bits: usize) -> usize {
    let mut result = 0;
    for i in 0..n_bits {
        result |= ((x >> i) & 1) << (n_bits - 1 - i);
    }
    result
}

pub fn transposed_par_iter_mut<A: Send + Sync, const N: usize>(
    array: &mut [Vec<A>; N], // all vectors must have the same length
) -> impl IndexedParallelIterator<Item = [&mut A; N]> + '_ {
    let len = array[0].len();
    let data_ptrs: [AtomicPtr<A>; N] = array.each_mut().map(|v| AtomicPtr::new(v.as_mut_ptr()));

    (0..len)
        .into_par_iter()
        .map(move |i| unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].load(Ordering::Relaxed).add(i)) })
}

#[derive(Debug)]
pub enum VecOrSlice<'a, T> {
    Vec(Vec<T>),
    Slice(&'a [T]),
}

impl<'a, T> VecOrSlice<'a, T> {
    pub fn as_slice(&self) -> &[T] {
        match self {
            VecOrSlice::Vec(v) => v.as_slice(),
            VecOrSlice::Slice(s) => s,
        }
    }
}

pub fn collect_refs<T>(vecs: &[Vec<T>]) -> Vec<&[T]> {
    vecs.iter().map(Vec::as_slice).collect()
}

#[derive(Debug, Clone, Default)]
pub struct Counter(usize);

impl Counter {
    pub fn get_next(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }

    pub fn new() -> Self {
        Self(0)
    }
}
