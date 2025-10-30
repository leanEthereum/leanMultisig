use p3_field::{BasedVectorSpace, ExtensionField, Field, dot_product};
use rayon::prelude::*;

use multilinear_toolkit::prelude::*;
use tracing::instrument;

pub fn transmute_slice<Before, After>(slice: &[Before]) -> &[After] {
    let new_len = std::mem::size_of_val(slice) / std::mem::size_of::<After>();
    assert_eq!(
        std::mem::size_of_val(slice),
        new_len * std::mem::size_of::<After>()
    );
    assert_eq!(slice.as_ptr() as usize % std::mem::align_of::<After>(), 0);
    unsafe { std::slice::from_raw_parts(slice.as_ptr() as *const After, new_len) }
}

pub fn left_ref<A>(slice: &[A]) -> &[A] {
    assert!(slice.len().is_multiple_of(2));
    let mid = slice.len() / 2;
    &slice[..mid]
}

pub fn right_ref<A>(slice: &[A]) -> &[A] {
    assert!(slice.len().is_multiple_of(2));
    let mid = slice.len() / 2;
    &slice[mid..]
}

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

pub fn field_slice_as_base<F: Field, EF: ExtensionField<F>>(slice: &[EF]) -> Option<Vec<F>> {
    slice.par_iter().map(|x| x.as_base()).collect()
}

pub fn transpose_slice_to_basis_coefficients<F: Field, EF: ExtensionField<F>>(
    slice: &[EF],
) -> Vec<Vec<F>> {
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
    (0..bit_count)
        .rev()
        .map(|i| (value >> i) & 1 == 1)
        .collect()
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

#[macro_export]
macro_rules! assert_eq_many {
    ($first:expr, $($rest:expr),+ $(,)?) => {
        {
            let first_val = $first;
            $(
                assert_eq!(first_val, $rest,
                    "assertion failed: `(left == right)`\n  left: `{:?}`,\n right: `{:?}`",
                    first_val, $rest);
            )+
        }
    };
}

pub fn finger_print<F: Field, EF: ExtensionField<F>>(
    table_index: usize,
    data: &[F],
    challenge: EF,
) -> EF {
    dot_product::<EF, _, _>(challenge.powers().skip(1), data.iter().copied())
        + F::from_usize(table_index)
}

pub fn powers_const<F: Field, const N: usize>(base: F) -> [F; N] {
    base.powers().collect_n(N).try_into().unwrap()
}

#[instrument(skip_all)]
pub fn transpose<F: Copy + Send + Sync>(
    matrix: &[F],
    width: usize,
    column_extra_capacity: usize,
) -> Vec<Vec<F>> {
    assert!((matrix.len().is_multiple_of(width)));
    let height = matrix.len() / width;
    let res = vec![
        {
            let mut vec = Vec::<F>::with_capacity(height + column_extra_capacity);
            #[allow(clippy::uninit_vec)]
            unsafe {
                vec.set_len(height);
            }
            vec
        };
        width
    ];
    matrix
        .par_chunks_exact(width)
        .enumerate()
        .for_each(|(row, chunk)| {
            for (&value, col) in chunk.iter().zip(&res) {
                unsafe {
                    let ptr = col.as_ptr() as *mut F;
                    ptr.add(row).write(value);
                }
            }
        });
    res
}

struct SendPtr<T>(*mut T);
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

pub fn transposed_par_iter_mut<A: Send + Sync, const N: usize>(
    array: &mut [Vec<A>; N], // all vectors must have the same length
) -> impl IndexedParallelIterator<Item = [&mut A; N]> + '_ {
    let len = array[0].len();
    let data_ptrs: [SendPtr<A>; N] = array.each_mut().map(|v| SendPtr(v.as_mut_ptr()));

    (0..len)
        .into_par_iter()
        .map(move |i| unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].0.add(i)) })
}
