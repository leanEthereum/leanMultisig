// Credits:
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::array;

use field::PackedValue;
use rayon::prelude::*;

use crate::Permutation;

pub const DIGEST_ELEMS: usize = 8;

/// A Merkle tree storing only the digest layers (no leaf data).
#[derive(Debug, Clone)]
pub struct MerkleTree<F, const DIGEST_ELEMS: usize> {
    pub digest_layers: Vec<Vec<[F; DIGEST_ELEMS]>>,
}

impl<F: Clone + Copy + Default + Send + Sync, const DIGEST_ELEMS: usize> MerkleTree<F, DIGEST_ELEMS> {
    /// Build a Merkle tree from a pre-computed first digest layer.
    pub fn from_first_layer<P, Perm, const WIDTH: usize>(perm: &Perm, first_layer: Vec<[F; DIGEST_ELEMS]>) -> Self
    where
        P: PackedValue<Value = F> + Default,
        Perm: Permutation<[F; WIDTH]> + Permutation<[P; WIDTH]>,
    {
        let mut digest_layers = vec![first_layer];
        loop {
            let prev_layer = digest_layers.last().unwrap().as_slice();
            if prev_layer.len() == 1 {
                break;
            }
            digest_layers.push(compress_layer::<P, Perm, DIGEST_ELEMS, WIDTH>(prev_layer, perm));
        }
        Self { digest_layers }
    }

    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.digest_layers.last().unwrap()[0]
    }

    /// Returns the sibling digests along the path from leaf to root.
    pub fn open_siblings(&self, index: usize, log_height: usize) -> Vec<[F; DIGEST_ELEMS]> {
        (0..log_height)
            .map(|i| self.digest_layers[i][(index >> i) ^ 1])
            .collect()
    }
}

pub fn compress_layer<P, Perm, const DIGEST_ELEMS: usize, const WIDTH: usize>(
    prev_layer: &[[P::Value; DIGEST_ELEMS]],
    perm: &Perm,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Perm: Permutation<[P::Value; WIDTH]> + Permutation<[P; WIDTH]>,
{
    let width = P::WIDTH;
    let next_len_padded = if prev_layer.len() == 2 {
        1
    } else {
        (prev_layer.len() / 2 + 1) & !1
    };
    let next_len = prev_layer.len() / 2;

    let default_digest = [P::Value::default(); DIGEST_ELEMS];
    let mut next_digests = vec![default_digest; next_len_padded];

    next_digests[0..next_len]
        .par_chunks_exact_mut(width)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row = i * width;
            let left = array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row + k)][j]));
            let right = array::from_fn(|j| P::from_fn(|k| prev_layer[2 * (first_row + k) + 1][j]));
            let packed_digest = crate::compress(perm, [left, right]);
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    for i in (next_len / width * width)..next_len {
        let left = prev_layer[2 * i];
        let right = prev_layer[2 * i + 1];
        next_digests[i] = crate::compress(perm, [left, right]);
    }

    next_digests
}

pub fn merkle_verify<F, Perm, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    commit: &[F; DIGEST_ELEMS],
    log_height: usize,
    mut index: usize,
    opened_values: &[F],
    opening_proof: &[[F; DIGEST_ELEMS]],
) -> bool
where
    F: Default + Copy + PartialEq,
    Perm: Permutation<[F; WIDTH]>,
{
    if opening_proof.len() != log_height {
        return false;
    }

    let mut root = crate::hash_slice::<_, _, WIDTH, RATE, DIGEST_ELEMS>(perm, opened_values);

    for &sibling in opening_proof.iter() {
        let (left, right) = if index & 1 == 0 {
            (root, sibling)
        } else {
            (sibling, root)
        };
        root = crate::compress(perm, [left, right]);
        index >>= 1;
    }

    commit == &root
}

#[inline]
pub fn unpack_array<P: PackedValue, const N: usize>(packed_digest: [P; N]) -> impl Iterator<Item = [P::Value; N]> {
    (0..P::WIDTH).map(move |j| packed_digest.map(|p| p.as_slice()[j]))
}
