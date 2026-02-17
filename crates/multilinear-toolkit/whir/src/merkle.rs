// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::any::TypeId;
use std::array;

use field::BasedVectorSpace;
use field::ExtensionField;
use field::Field;
use field::PackedValue;
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon2_16};
use poly::*;

use rayon::prelude::*;
use symetric::Permutation;
use tracing::instrument;
use utils::log2_strict_usize;

use crate::DenseMatrix;
use crate::Dimensions;
use crate::FlatMatrixView;
use crate::Matrix;
use crate::log2_ceil_usize;
pub const DIGEST_ELEMS: usize = 8;

pub(crate) type RoundMerkleTree<F, EF> = MerkleTree<F, FlatMatrixView<F, EF, DenseMatrix<EF>>, DIGEST_ELEMS>;

pub(crate) fn merkle_commit<F: Field, EF: ExtensionField<F>>(
    matrix: DenseMatrix<EF>,
) -> ([F; DIGEST_ELEMS], RoundMerkleTree<F, EF>) {
    let perm = default_koalabear_poseidon2_16();
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<QuinticExtensionFieldKB>>(matrix) };
        let view = FlatMatrixView::new(matrix);
        let tree = MerkleTree::new::<PFPacking<KoalaBear>, _, 16, 8>(&perm, view);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F, EF>>(tree) };
        (root, tree)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<KoalaBear>>(matrix) };
        let tree = MerkleTree::new::<PFPacking<KoalaBear>, _, 16, 8>(&perm, matrix);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F, EF>>(tree) };
        (root, tree)
    } else {
        unimplemented!()
    }
}

pub(crate) fn merkle_open<F: Field, EF: ExtensionField<F>>(
    merkle_tree: &RoundMerkleTree<F, EF>,
    index: usize,
) -> (Vec<EF>, Vec<[F; DIGEST_ELEMS]>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_tree =
            unsafe { std::mem::transmute::<_, &RoundMerkleTree<KoalaBear, QuinticExtensionFieldKB>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = QuinticExtensionFieldKB::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<KoalaBear, KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = KoalaBear::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else {
        unimplemented!()
    }
}

pub(crate) fn merkle_verify<F: Field, EF: ExtensionField<F>>(
    merkle_root: [F; DIGEST_ELEMS],
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<[F; DIGEST_ELEMS]>,
) -> bool {
    let perm = default_koalabear_poseidon2_16();
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [KoalaBear; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<QuinticExtensionFieldKB>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[KoalaBear; DIGEST_ELEMS]>>(proof) };
        let base_data = QuinticExtensionFieldKB::flatten_to_base(data);
        let base_dim = Dimensions {
            width: dimension.width * <QuinticExtensionFieldKB as BasedVectorSpace<KoalaBear>>::DIMENSION,
            height: dimension.height,
        };
        verify::<_, _, DIGEST_ELEMS, 16, 8>(&perm, &merkle_root, base_dim, index, &base_data, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [KoalaBear; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<KoalaBear>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[KoalaBear; DIGEST_ELEMS]>>(proof) };
        let base_data = KoalaBear::flatten_to_base(data);
        let base_dim = Dimensions {
            width: dimension.width * <KoalaBear as BasedVectorSpace<KoalaBear>>::DIMENSION,
            height: dimension.height,
        };
        verify::<_, _, DIGEST_ELEMS, 16, 8>(&perm, &merkle_root, base_dim, index, &base_data, proof)
    } else {
        unimplemented!()
    }
}

fn verify<F, Perm, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    commit: &[F; DIGEST_ELEMS],
    dimension: Dimensions,
    mut index: usize,
    opened_values: &[F],
    opening_proof: &[[F; DIGEST_ELEMS]],
) -> bool
where
    F: Default + Copy + PartialEq,
    Perm: Permutation<[F; WIDTH]>,
{
    let max_height = dimension.height.next_power_of_two();
    let log_max_height = log2_strict_usize(max_height);
    if opening_proof.len() != log_max_height {
        return false;
    }

    let mut root = symetric::hash_slice::<_, _, WIDTH, RATE, DIGEST_ELEMS>(perm, opened_values);

    for &sibling in opening_proof.iter() {
        let (left, right) = if index & 1 == 0 {
            (root, sibling)
        } else {
            (sibling, root)
        };
        root = symetric::compress(perm, [left, right]);
        index >>= 1;
    }

    commit == &root
}

#[derive(Debug, Clone)]
pub struct MerkleTree<F, M, const DIGEST_ELEMS: usize> {
    pub(crate) leaf: M,
    pub(crate) digest_layers: Vec<Vec<[F; DIGEST_ELEMS]>>,
}

impl<F: Clone + Copy + Default + Send + Sync, M: Matrix<F>, const DIGEST_ELEMS: usize> MerkleTree<F, M, DIGEST_ELEMS> {
    #[instrument(name = "build merkle tree", skip_all)]
    pub fn new<P, Perm, const WIDTH: usize, const RATE: usize>(perm: &Perm, leaf: M) -> Self
    where
        P: PackedValue<Value = F> + Default,
        Perm: Permutation<[F; WIDTH]> + Permutation<[P; WIDTH]>,
    {
        let mut digest_layers = vec![first_digest_layer::<P, Perm, _, DIGEST_ELEMS, WIDTH, RATE>(perm, &leaf)];
        loop {
            let prev_layer = digest_layers.last().unwrap().as_slice();
            if prev_layer.len() == 1 {
                break;
            }
            digest_layers.push(compress_layer::<P, Perm, DIGEST_ELEMS, WIDTH>(prev_layer, perm));
        }

        Self { leaf, digest_layers }
    }

    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.digest_layers.last().unwrap()[0]
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<[F; DIGEST_ELEMS]>) {
        let log_height = log2_ceil_usize(self.leaf.height());

        let opening = self.leaf.row(index).unwrap().into_iter().collect();

        let proof = (0..log_height)
            .map(|i| self.digest_layers[i][(index >> i) ^ 1])
            .collect();

        (opening, proof)
    }
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn first_digest_layer<P, Perm, M, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    matrix: &M,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Perm: Permutation<[P::Value; WIDTH]> + Permutation<[P; WIDTH]>,
    M: Matrix<P::Value>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    let height_padded = if height == 1 { 1 } else { height + height % 2 };

    let default_digest = [P::Value::default(); DIGEST_ELEMS];
    let mut digests = vec![default_digest; height_padded];

    digests[0..height]
        .par_chunks_exact_mut(width)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row = i * width;
            let packed_digest: [P; DIGEST_ELEMS] = symetric::hash_iter::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(
                perm,
                matrix.vertically_packed_row(first_row),
            );
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    #[allow(clippy::needless_range_loop)]
    for i in ((height / width) * width)..height {
        unsafe {
            digests[i] = symetric::hash_iter::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(perm, matrix.row_unchecked(i));
        }
    }

    digests
}

fn compress_layer<P, Perm, const DIGEST_ELEMS: usize, const WIDTH: usize>(
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
            let packed_digest = symetric::compress(perm, [left, right]);
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    for i in (next_len / width * width)..next_len {
        let left = prev_layer[2 * i];
        let right = prev_layer[2 * i + 1];
        next_digests[i] = symetric::compress(perm, [left, right]);
    }

    next_digests
}

#[inline]
fn unpack_array<P: PackedValue, const N: usize>(packed_digest: [P; N]) -> impl Iterator<Item = [P::Value; N]> {
    (0..P::WIDTH).map(move |j| packed_digest.map(|p| p.as_slice()[j]))
}
