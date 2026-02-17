use std::{
    iter::Sum,
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
    if slice.len() < PARALLEL_THRESHOLD {
        slice
            .chunks_exact(width)
            .map(EFPacking::<EF>::from_ext_slice)
            .collect::<Vec<_>>()
    } else {
        slice
            .par_chunks_exact(width)
            .map(EFPacking::<EF>::from_ext_slice)
            .collect::<Vec<_>>()
    }
}

pub fn unpack_extension<EF: ExtensionField<PF<EF>>>(vec: &[EFPacking<EF>]) -> Vec<EF> {
    let width = packing_width::<EF>();
    let total_elements = vec.len() * width;
    if total_elements < PARALLEL_THRESHOLD {
        vec.iter()
            .flat_map(|x| {
                let packed_coeffs = x.as_basis_coefficients_slice();
                (0..width)
                    .map(|i| EF::from_basis_coefficients_fn(|j| packed_coeffs[j].as_slice()[i]))
                    .collect::<Vec<_>>()
            })
            .collect()
    } else {
        vec.par_iter()
            .flat_map(|x| {
                let packed_coeffs = x.as_basis_coefficients_slice();
                (0..width)
                    .map(|i| EF::from_basis_coefficients_fn(|j| packed_coeffs[j].as_slice()[i]))
                    .collect::<Vec<_>>()
            })
            .collect()
    }
}

pub const fn packing_log_width<EF: Field>() -> usize {
    packing_width::<EF>().ilog2() as usize
}

pub const fn packing_width<EF: Field>() -> usize {
    PFPacking::<EF>::WIDTH
}

pub fn batch_fold_multilinears<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync + Sum,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    polys: &[&[IF]],
    scalars: &[EF],
    mul_if_of: F,
) -> Vec<Vec<OF>> {
    let total_size: usize = polys.iter().map(|p| p.len()).sum();
    if total_size < PARALLEL_THRESHOLD {
        polys
            .iter()
            .map(|poly| fold_multilinear(poly, scalars, &mul_if_of))
            .collect()
    } else {
        polys
            .par_iter()
            .map(|poly| fold_multilinear(poly, scalars, &mul_if_of))
            .collect()
    }
}

pub fn fold_multilinear<
    EF: PrimeCharacteristicRing + Copy + Send + Sync,
    IF: Copy + Sub<Output = IF> + Send + Sync,
    OF: Copy + Add<IF, Output = OF> + Send + Sync + Sum,
    F: Fn(IF, EF) -> OF + Sync + Send,
>(
    m: &[IF],
    scalars: &[EF],
    mul_if_of: &F,
) -> Vec<OF> {
    assert!(scalars.len().is_power_of_two() && scalars.len() <= m.len());
    let new_size = m.len() / scalars.len();
    let mut res = unsafe { uninitialized_vec(new_size) };

    if new_size < PARALLEL_THRESHOLD {
        if scalars.len() == 2 {
            assert_eq!(scalars[0], EF::ONE - scalars[1]);
            let alpha = scalars[1];
            for i in 0..new_size {
                res[i] = mul_if_of(m[i + new_size] - m[i], alpha) + m[i];
            }
        } else {
            for i in 0..new_size {
                res[i] = scalars
                    .iter()
                    .enumerate()
                    .map(|(j, s)| mul_if_of(m[i + j * new_size], *s))
                    .sum();
            }
        }
    } else {
        if scalars.len() == 2 {
            assert_eq!(scalars[0], EF::ONE - scalars[1]);
            let alpha = scalars[1];
            (0..new_size)
                .into_par_iter()
                .with_min_len(PARALLEL_THRESHOLD)
                .map(|i| mul_if_of(m[i + new_size] - m[i], alpha) + m[i])
                .collect_into_vec(&mut res);
        } else {
            (0..new_size)
                .into_par_iter()
                .with_min_len(PARALLEL_THRESHOLD)
                .map(|i| {
                    scalars
                        .iter()
                        .enumerate()
                        .map(|(j, s)| mul_if_of(m[i + j * new_size], *s))
                        .sum()
                })
                .collect_into_vec(&mut res);
        }
    }
    res
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

pub fn parallel_clone<A: Clone + Send + Sync>(src: &[A], dst: &mut [A]) {
    if src.len() < PARALLEL_THRESHOLD {
        // sequential copy
        dst.clone_from_slice(src);
    } else {
        assert_eq!(src.len(), dst.len());
        let chunk_size = src.len() / rayon::current_num_threads().max(1);
        dst.par_chunks_mut(chunk_size)
            .zip(src.par_chunks(chunk_size))
            .for_each(|(d, s)| {
                d.clone_from_slice(s);
            });
    }
}

#[must_use]
pub fn parallel_clone_vec<A: Clone + Send + Sync>(vec: &[A]) -> Vec<A> {
    let mut res = unsafe { uninitialized_vec(vec.len()) };
    parallel_clone(vec, &mut res);
    res
}

pub fn dot_product_ef_packed_par<EF: ExtensionField<PF<EF>>, R: Sync + Send + Copy>(a: &[EFPacking<EF>], b: &[R]) -> EF
where
    EFPacking<EF>: Algebra<R>,
{
    assert_eq!(a.len(), b.len());
    let total_elements = a.len() * packing_width::<EF>();
    let res_packed: EFPacking<EF> = if total_elements < PARALLEL_THRESHOLD {
        a.iter().zip(b.iter()).map(|(&x, &y)| x * y).sum::<EFPacking<EF>>()
    } else {
        a.par_iter()
            .zip(b.par_iter())
            .map(|(&x, &y)| x * y)
            .sum::<EFPacking<EF>>()
    };
    unpack_extension(&[res_packed]).into_iter().sum()
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

pub fn par_iter_split_4<'a, A: Sync + Send>(
    u: &'a [A],
) -> Zip<Zip<Iter<'a, A>, Iter<'a, A>>, Zip<Iter<'a, A>, Iter<'a, A>>> {
    let n = u.len();
    assert!(n % 4 == 0);
    let [u_ll, u_lr, u_rl, u_rr] = split_at_many(u, &[n / 4, n / 2, 3 * n / 4]).try_into().ok().unwrap();
    (u_ll.par_iter().zip(u_lr)).zip(u_rl.par_iter().zip(u_rr.par_iter()))
}

pub fn par_iter_split_2<'a, A: Sync + Send>(u: &'a [A]) -> Zip<Iter<'a, A>, Iter<'a, A>> {
    par_iter_split_2_capped(u, 0..u.len() / 2)
}

pub fn par_iter_split_2_capped<'a, A: Sync + Send>(u: &'a [A], range: Range<usize>) -> Zip<Iter<'a, A>, Iter<'a, A>> {
    let n = u.len();
    assert!(n % 2 == 0);
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
    assert!(n % 2 == 0);
    let (u_left, u_right) = u.split_at_mut(n / 2);
    u_left[range.clone()].par_iter_mut().zip(u_right[range].par_iter_mut())
}

pub fn par_zip_fold_2<'a, 'b, A: Sync + Send, B: Sync + Send>(
    u: &'a [A],
    folded: &'b mut [B],
) -> Zip<Zip<Zip<Iter<'a, A>, Iter<'a, A>>, Zip<Iter<'a, A>, Iter<'a, A>>>, Zip<IterMut<'b, B>, IterMut<'b, B>>> {
    let n = u.len();
    assert!(n % 4 == 0);
    assert_eq!(folded.len(), n / 2);
    par_iter_split_4(u).zip(par_iter_mut_split_2(folded))
}

// Sequential

pub fn iter_split_2<'a, A>(u: &'a [A]) -> impl Iterator<Item = (&'a A, &'a A)> {
    let n = u.len();
    assert!(n % 2 == 0);
    let (u_left, u_right) = u.split_at(n / 2);
    u_left.iter().zip(u_right.iter())
}

pub fn iter_split_4<'a, A>(u: &'a [A]) -> impl Iterator<Item = ((&'a A, &'a A), (&'a A, &'a A))> {
    let n = u.len();
    assert!(n % 4 == 0);
    let (u_left, u_right) = u.split_at(n / 2);
    let (u_ll, u_lr) = u_left.split_at(n / 4);
    let (u_rl, u_rr) = u_right.split_at(n / 4);
    u_ll.iter().zip(u_lr.iter()).zip(u_rl.iter().zip(u_rr.iter()))
}

pub fn iter_mut_split_2<'a, A>(u: &'a mut [A]) -> impl Iterator<Item = (&'a mut A, &'a mut A)> {
    let n = u.len();
    assert!(n % 2 == 0);
    let (u_left, u_right) = u.split_at_mut(n / 2);
    u_left.iter_mut().zip(u_right.iter_mut())
}

pub fn zip_fold_2<'a, 'b, A, B>(
    u: &'a [A],
    folded: &'b mut [B],
) -> impl Iterator<Item = (((&'a A, &'a A), (&'a A, &'a A)), (&'b mut B, &'b mut B))> {
    let n = u.len();
    assert!(n % 4 == 0);
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

#[cfg(test)]
mod tests {
    use koala_bear::{KoalaBear, QuinticExtensionFieldKB};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use super::*;
    type F = KoalaBear;
    type EF = QuinticExtensionFieldKB;

    #[test]
    fn test_dot_product_ef_f_packed() {
        let n = 1 << 20;
        let mut rng = StdRng::seed_from_u64(0);
        let a: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let b: Vec<F> = (0..n).map(|_| rng.random()).collect();
        assert_eq!(
            dot_product_ef_packed_par::<EF, _>(&pack_extension(&a), PFPacking::<EF>::pack_slice(&b)),
            a.par_iter().zip(b.par_iter()).map(|(&x, &y)| x * y).sum::<EF>()
        );
    }

    #[test]
    fn test_dot_product_ef_ef_packed() {
        let n = 1 << 20;
        let mut rng = StdRng::seed_from_u64(0);
        let a: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        let b: Vec<EF> = (0..n).map(|_| rng.random()).collect();
        assert_eq!(
            dot_product_ef_packed_par::<EF, _>(&pack_extension(&a), &pack_extension(&b),),
            a.par_iter().zip(b.par_iter()).map(|(&x, &y)| x * y).sum::<EF>()
        );
    }
}
