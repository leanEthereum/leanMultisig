use std::{
    mem::ManuallyDrop,
    ops::{Add, Range, Sub},
};

use field::*;
use rayon::{
    iter::Zip,
    prelude::*,
    slice::{Iter, IterMut},
};

use crate::{EFPacking, PF, PFPacking};

pub const PARALLEL_THRESHOLD: usize = 1 << 9;

pub fn pack_extension<EF: ExtensionField<PF<EF>>>(slice: &[EF]) -> Vec<EFPacking<EF>> {
    let width = packing_width::<EF>();
    let n_packed = slice.len() / width;
    let mut out: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(n_packed) };
    let write = |slot: &mut EFPacking<EF>, chunk: &[EF]| {
        *slot = EFPacking::<EF>::from_ext_slice(chunk);
    };
    if slice.len() < PARALLEL_THRESHOLD {
        for (slot, chunk) in out.iter_mut().zip(slice.chunks_exact(width)) {
            write(slot, chunk);
        }
    } else {
        out.par_iter_mut()
            .zip(slice.par_chunks_exact(width))
            .for_each(|(slot, chunk)| write(slot, chunk));
    }
    out
}

pub fn unpack_extension<EF: ExtensionField<PF<EF>>>(vec: &[EFPacking<EF>]) -> Vec<EF> {
    let width = packing_width::<EF>();
    let total = vec.len() * width;
    let mut out: Vec<EF> = unsafe { uninitialized_vec(total) };
    let write = |out_chunk: &mut [EF], x: &EFPacking<EF>| {
        let packed_coeffs = x.as_basis_coefficients_slice();
        for (lane, slot) in out_chunk.iter_mut().enumerate() {
            *slot = EF::from_basis_coefficients_fn(|j| packed_coeffs[j].as_slice()[lane]);
        }
    };
    if total < PARALLEL_THRESHOLD {
        for (chunk, x) in out.chunks_exact_mut(width).zip(vec.iter()) {
            write(chunk, x);
        }
    } else {
        out.par_chunks_exact_mut(width)
            .zip(vec.par_iter())
            .for_each(|(chunk, x)| write(chunk, x));
    }
    out
}

pub const fn packing_log_width<EF: Field>() -> usize {
    packing_width::<EF>().ilog2() as usize
}

pub const fn packing_width<EF: Field>() -> usize {
    PFPacking::<EF>::WIDTH
}

pub const fn must_unpack_multilinears<EF: Field>(n_vars: usize) -> bool {
    n_vars <= 1 + packing_log_width::<EF>()
}

pub fn batch_fold_multilinears<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    polys: &[&[IF]],
    alpha: EF,
    mul_if_of: F,
) -> Vec<Vec<OF>> {
    let total_size: usize = polys.iter().map(|p| p.len()).sum();
    if total_size < PARALLEL_THRESHOLD {
        polys
            .iter()
            .map(|poly| fold_multilinear(poly, alpha, &mul_if_of))
            .collect()
    } else {
        polys
            .par_iter()
            .map(|poly| fold_multilinear(poly, alpha, &mul_if_of))
            .collect()
    }
}

pub fn fold_multilinear_lsb<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    Mul: Fn(IF, EF) -> OF + Sync + Send,
>(
    m: &[IF],
    alpha: EF,
    mul_if_of: &Mul,
) -> Vec<OF> {
    let new_size = m.len() / 2;
    let mut res = unsafe { uninitialized_vec(new_size) };
    let compute = |(c, r_v): (&[IF], &mut OF)| {
        *r_v = mul_if_of(c[1] - c[0], alpha) + c[0];
    };
    if new_size < PARALLEL_THRESHOLD {
        m.chunks_exact(2).zip(res.iter_mut()).for_each(compute);
    } else {
        m.par_chunks_exact(2).zip(res.par_iter_mut()).for_each(compute);
    }
    res
}

pub fn fold_multilinear_at_bit<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    Mul: Fn(IF, EF) -> OF + Sync + Send,
>(
    m: &[IF],
    alpha: EF,
    bit: usize,
    mul_if_of: &Mul,
) -> Vec<OF> {
    let new_size = m.len() / 2;
    assert!(m.len() >= 2 * (1 << bit), "bit out of range for slice length");

    if bit == 0 {
        return fold_multilinear_lsb(m, alpha, mul_if_of);
    }

    let stride = 1usize << bit;
    let lo_mask = stride - 1;
    let mut res = unsafe { uninitialized_vec(new_size) };

    let compute = |new_j: usize| {
        let i_hi = new_j >> bit;
        let i_lo = new_j & lo_mask;
        let i0 = (i_hi << (bit + 1)) | i_lo;
        let i1 = i0 | stride;
        mul_if_of(m[i1] - m[i0], alpha) + m[i0]
    };

    if new_size < PARALLEL_THRESHOLD {
        for (new_j, res_v) in res.iter_mut().enumerate() {
            *res_v = compute(new_j);
        }
    } else {
        (0..new_size)
            .into_par_iter()
            .with_min_len(PARALLEL_THRESHOLD)
            .map(compute)
            .collect_into_vec(&mut res);
    }
    res
}

pub fn fold_multilinear<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    m: &[IF],
    alpha: EF,
    mul_if_of: &F,
) -> Vec<OF> {
    let new_size = m.len() / 2;
    let mut res = unsafe { uninitialized_vec(new_size) };

    if new_size < PARALLEL_THRESHOLD {
        for i in 0..new_size {
            res[i] = mul_if_of(m[i + new_size] - m[i], alpha) + m[i];
        }
    } else {
        (0..new_size)
            .into_par_iter()
            .with_min_len(PARALLEL_THRESHOLD)
            .map(|i| mul_if_of(m[i + new_size] - m[i], alpha) + m[i])
            .collect_into_vec(&mut res);
    }
    res
}

pub fn batch_fold_multilinears_at_bit<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    polys: &[&[IF]],
    alpha: EF,
    bit: usize,
    mul_if_of: F,
) -> Vec<Vec<OF>> {
    let total_size: usize = polys.iter().map(|p| p.len()).sum();
    if total_size < PARALLEL_THRESHOLD {
        polys
            .iter()
            .map(|poly| fold_multilinear_at_bit(poly, alpha, bit, &mul_if_of))
            .collect()
    } else {
        polys
            .par_iter()
            .map(|poly| fold_multilinear_at_bit(poly, alpha, bit, &mul_if_of))
            .collect()
    }
}

/// Returns a vector of uninitialized elements of type `A` with the specified length.
/// # Safety
/// Entries should be overwritten before use.
#[must_use]
pub unsafe fn uninitialized_vec<A>(len: usize) -> Vec<A> {
    #[allow(clippy::uninit_vec)]
    unsafe {
        let mut vec = Vec::with_capacity(len);
        vec.set_len(len);
        vec
    }
}

pub fn split_at_many<'a, A>(slice: &'a [A], indices: &[usize]) -> Vec<&'a [A]> {
    for i in 0..indices.len() {
        if i > 0 {
            assert!(indices[i] > indices[i - 1]);
        }
        assert!(indices[i] <= slice.len());
    }

    if indices.is_empty() {
        return vec![slice];
    }

    let mut result = Vec::with_capacity(indices.len() + 1);
    let mut current_slice = slice;
    let mut prev_idx = 0;

    for &idx in indices {
        let adjusted_idx = idx - prev_idx;
        let (left, right) = current_slice.split_at(adjusted_idx);
        result.push(left);
        current_slice = right;
        prev_idx = idx;
    }

    result.push(current_slice);

    result
}

pub fn split_at_mut_many<'a, A>(slice: &'a mut [A], indices: &[usize]) -> Vec<&'a mut [A]> {
    for i in 0..indices.len() {
        if i > 0 {
            assert!(indices[i] > indices[i - 1]);
        }
        assert!(indices[i] <= slice.len());
    }

    if indices.is_empty() {
        return vec![slice];
    }

    let mut result = Vec::with_capacity(indices.len() + 1);
    let mut current_slice = slice;
    let mut prev_idx = 0;

    for &idx in indices {
        let adjusted_idx = idx - prev_idx;
        let (left, right) = current_slice.split_at_mut(adjusted_idx);
        result.push(left);
        current_slice = right;
        prev_idx = idx;
    }

    result.push(current_slice);

    result
}

// Parallel

#[allow(clippy::type_complexity)]
pub fn par_iter_split_4<'a, A: Sync + Send>(
    u: &'a [A],
) -> Zip<Zip<Iter<'a, A>, Iter<'a, A>>, Zip<Iter<'a, A>, Iter<'a, A>>> {
    let n = u.len();
    assert!(n.is_multiple_of(4));
    let [u_ll, u_lr, u_rl, u_rr] = split_at_many(u, &[n / 4, n / 2, 3 * n / 4]).try_into().ok().unwrap();
    (u_ll.par_iter().zip(u_lr)).zip(u_rl.par_iter().zip(u_rr.par_iter()))
}

pub fn par_iter_split_2<'a, A: Sync + Send>(u: &'a [A]) -> Zip<Iter<'a, A>, Iter<'a, A>> {
    par_iter_split_2_capped(u, 0..u.len() / 2)
}

pub fn par_iter_split_2_capped<'a, A: Sync + Send>(u: &'a [A], range: Range<usize>) -> Zip<Iter<'a, A>, Iter<'a, A>> {
    let n = u.len();
    assert!(n.is_multiple_of(2));
    let (u_left, u_right) = u.split_at(n / 2);
    u_left[range.clone()].par_iter().zip(u_right[range.clone()].par_iter())
}

pub fn par_iter_mut_split_2<'a, A: Sync + Send>(u: &'a mut [A]) -> Zip<IterMut<'a, A>, IterMut<'a, A>> {
    par_iter_mut_split_2_capped(u, 0..u.len() / 2)
}

pub fn par_iter_mut_split_2_capped<'a, A: Sync + Send>(
    u: &'a mut [A],
    range: Range<usize>,
) -> Zip<IterMut<'a, A>, IterMut<'a, A>> {
    let n = u.len();
    assert!(n.is_multiple_of(2));
    let (u_left, u_right) = u.split_at_mut(n / 2);
    u_left[range.clone()].par_iter_mut().zip(u_right[range].par_iter_mut())
}

#[allow(clippy::type_complexity)]
pub fn par_zip_fold_2<'a, 'b, A: Sync + Send, B: Sync + Send>(
    u: &'a [A],
    folded: &'b mut [B],
) -> Zip<Zip<Zip<Iter<'a, A>, Iter<'a, A>>, Zip<Iter<'a, A>, Iter<'a, A>>>, Zip<IterMut<'b, B>, IterMut<'b, B>>> {
    let n = u.len();
    assert!(n.is_multiple_of(4));
    assert_eq!(folded.len(), n / 2);
    par_iter_split_4(u).zip(par_iter_mut_split_2(folded))
}

// Sequential

pub fn iter_split_2<A>(u: &[A]) -> impl Iterator<Item = (&A, &A)> {
    let n = u.len();
    assert!(n.is_multiple_of(2));
    let (u_left, u_right) = u.split_at(n / 2);
    u_left.iter().zip(u_right.iter())
}

pub fn iter_split_4<A>(u: &[A]) -> impl Iterator<Item = ((&A, &A), (&A, &A))> {
    let n = u.len();
    assert!(n.is_multiple_of(4));
    let (u_left, u_right) = u.split_at(n / 2);
    let (u_ll, u_lr) = u_left.split_at(n / 4);
    let (u_rl, u_rr) = u_right.split_at(n / 4);
    u_ll.iter().zip(u_lr.iter()).zip(u_rl.iter().zip(u_rr.iter()))
}

pub fn iter_mut_split_2<A>(u: &mut [A]) -> impl Iterator<Item = (&mut A, &mut A)> {
    let n = u.len();
    assert!(n.is_multiple_of(2));
    let (u_left, u_right) = u.split_at_mut(n / 2);
    u_left.iter_mut().zip(u_right.iter_mut())
}

#[allow(clippy::type_complexity)]
pub fn zip_fold_2<'a, 'b, A, B>(
    u: &'a [A],
    folded: &'b mut [B],
) -> impl Iterator<Item = (((&'a A, &'a A), (&'a A, &'a A)), (&'b mut B, &'b mut B))> {
    let n = u.len();
    assert!(n.is_multiple_of(4));
    assert_eq!(folded.len(), n / 2);
    iter_split_4(u).zip(iter_mut_split_2(folded))
}

pub fn transmute_array<A, const N: usize, const M: usize>(input: [A; N]) -> [A; M] {
    assert_eq!(N, M, "Array sizes must match");

    unsafe {
        // Prevent input from being dropped
        let input = ManuallyDrop::new(input);

        // Read the array as a pointer and cast to the output type
        std::ptr::read(&*input as *const [A; N] as *const [A; M])
    }
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
