// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

/// A permutation in the mathematical sense (from symmetric).
pub trait Permutation<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn permute(&self, mut input: T) -> T {
        self.permute_mut(&mut input);
        input
    }

    fn permute_mut(&self, input: &mut T);
}

/// A permutation thought to be cryptographically secure.
pub trait CryptographicPermutation<T: Clone>: Permutation<T> {}

/// A marker trait for MDS permutations (from mds).
pub trait MdsPermutation<T: Clone, const WIDTH: usize>: Permutation<[T; WIDTH]> {}
