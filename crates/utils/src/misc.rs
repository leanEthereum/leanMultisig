use p3_field::{BasedVectorSpace, ExtensionField, Field, dot_product};
use rayon::prelude::*;

use crate::PF;

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

pub fn finger_print<F: Field, EF: ExtensionField<F>>(data: &[F], challenge: EF) -> EF {
    challenge + dot_product::<EF, _, _>(challenge.powers().skip(2), data.iter().copied())
}

pub fn powers_const<F: Field, const N: usize>(base: F) -> [F; N] {
    base.powers().collect_n(N).try_into().unwrap()
}
