// Credits:
// - whir-p3 (https://github.com/tcoratger/whir-p3) (MIT and Apache-2.0 licenses).
// - Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use std::any::TypeId;

use field::BasedVectorSpace;
use field::ExtensionField;
use field::Field;
use field::PackedValue;
use field::PrimeField32;
use koala_bear::{KoalaBear, QuinticExtensionFieldKB, default_koalabear_poseidon1_16};
use poly::*;

use rayon::prelude::*;
use symetric::Compression;
use symetric::merkle::MerkleTreeSha2;
use symetric::merkle::Sha256Digest;
use symetric::merkle::unpack_array;
use tracing::instrument;
use utils::log2_ceil_usize;

use crate::DenseMatrix;
use crate::Dimensions;
use crate::Matrix;
pub use symetric::DIGEST_ELEMS;

pub(crate) type RoundMerkleTree<F> = WhirMerkleTree<F, DenseMatrix<F>, DIGEST_ELEMS>;
pub(crate) type RoundMerkleTreeSha2<F> = WhirMerkleTreeSha2<F, DenseMatrix<F>>;

use sha2::{Digest, Sha256};

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_commit<F: Field, EF: ExtensionField<F>>(
    matrix: DenseMatrix<EF>,
    full_n_cols: usize,
    effective_n_cols: usize,
) -> ([F; DIGEST_ELEMS], RoundMerkleTree<F>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<QuinticExtensionFieldKB>>(matrix) };
        let dim = <QuinticExtensionFieldKB as BasedVectorSpace<KoalaBear>>::DIMENSION;
        let dft_base_width = matrix.width * dim;
        let full_base_width = full_n_cols * dim;
        let effective_base_width = effective_n_cols * dim;
        let base_values = QuinticExtensionFieldKB::flatten_to_base(matrix.values);
        let base_matrix = DenseMatrix::<KoalaBear>::new(base_values, dft_base_width);
        let tree = build_merkle_tree_koalabear(base_matrix, full_base_width, effective_base_width);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F>>(tree) };
        (root, tree)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<KoalaBear>>(matrix) };
        let tree = build_merkle_tree_koalabear(matrix, full_n_cols, effective_n_cols);
        let root: [_; DIGEST_ELEMS] = tree.root();
        let root = unsafe { std::mem::transmute_copy::<_, [F; DIGEST_ELEMS]>(&root) };
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTree<F>>(tree) };
        (root, tree)
    } else {
        unimplemented!()
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_commit_sha2<F: Field + PrimeField32, EF: ExtensionField<F>>(
    matrix: DenseMatrix<EF>,
    full_n_cols: usize,
    effective_n_cols: usize,
) -> (Sha256Digest, RoundMerkleTreeSha2<F>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<QuinticExtensionFieldKB>>(matrix) };
        let dim = <QuinticExtensionFieldKB as BasedVectorSpace<KoalaBear>>::DIMENSION;
        let dft_base_width = matrix.width * dim;
        let full_base_width = full_n_cols * dim;
        let effective_base_width = effective_n_cols * dim;
        let base_values = QuinticExtensionFieldKB::flatten_to_base(matrix.values);
        let base_matrix = DenseMatrix::<KoalaBear>::new(base_values, dft_base_width);
        let tree = build_merkle_tree_sha256(base_matrix, full_base_width, effective_base_width);
        let root = tree.root();
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTreeSha2<F>>(tree) };
        (root, tree)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let matrix = unsafe { std::mem::transmute::<_, DenseMatrix<KoalaBear>>(matrix) };
        let tree = build_merkle_tree_sha256(matrix, full_n_cols, effective_n_cols);
        let root = tree.root();
        let tree = unsafe { std::mem::transmute::<_, RoundMerkleTreeSha2<F>>(tree) };
        (root, tree)
    } else {
        unimplemented!()
    }
}

#[instrument(name = "build merkle tree", skip_all)]
fn build_merkle_tree_koalabear(
    leaf: DenseMatrix<KoalaBear>,
    full_base_width: usize,
    effective_base_width: usize,
) -> RoundMerkleTree<KoalaBear> {
    let perm = default_koalabear_poseidon1_16();
    let n_zero_suffix_rate_chunks = (full_base_width - effective_base_width) / 8;
    let first_layer = if n_zero_suffix_rate_chunks >= 2 {
        let scalar_state = symetric::precompute_zero_suffix_state::<KoalaBear, _, 16, 8, DIGEST_ELEMS>(
            &perm,
            n_zero_suffix_rate_chunks,
        );
        let packed_state: [PFPacking<KoalaBear>; 16] =
            std::array::from_fn(|i| PFPacking::<KoalaBear>::from_fn(|_| scalar_state[i]));
        first_digest_layer_with_initial_state::<PFPacking<KoalaBear>, _, _, DIGEST_ELEMS, 16, 8>(
            &perm,
            &leaf,
            &packed_state,
            effective_base_width,
        )
    } else {
        first_digest_layer::<PFPacking<KoalaBear>, _, _, DIGEST_ELEMS, 16, 8>(&perm, &leaf, full_base_width)
    };
    let tree = symetric::merkle::MerkleTree::from_first_layer::<PFPacking<KoalaBear>, _, 16>(&perm, first_layer);
    WhirMerkleTree {
        leaf,
        tree,
        full_leaf_base_width: full_base_width,
    }
}

#[instrument(name = "build merkle tree sha256", skip_all)]
fn build_merkle_tree_sha256(
    leaf: DenseMatrix<KoalaBear>,
    full_base_width: usize,
    effective_base_width: usize,
) -> RoundMerkleTreeSha2<KoalaBear> {
    WhirMerkleTreeSha2::new(leaf, full_base_width, effective_base_width)
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_open<F: Field, EF: ExtensionField<F>>(
    merkle_tree: &RoundMerkleTree<F>,
    index: usize,
) -> (Vec<EF>, Vec<[F; DIGEST_ELEMS]>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = QuinticExtensionFieldKB::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTree<KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = KoalaBear::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        let proof = unsafe { std::mem::transmute::<_, Vec<[F; DIGEST_ELEMS]>>(proof) };
        (leaf, proof)
    } else {
        unimplemented!()
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_open_sha2<F: Field + PrimeField32, EF: ExtensionField<F>>(
    merkle_tree: &RoundMerkleTreeSha2<F>,
    index: usize,
) -> (Vec<EF>, Vec<Sha256Digest>) {
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTreeSha2<KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = QuinticExtensionFieldKB::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        (leaf, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_tree = unsafe { std::mem::transmute::<_, &RoundMerkleTreeSha2<KoalaBear>>(merkle_tree) };
        let (inner_leaf, proof) = merkle_tree.open(index);
        let leaf = KoalaBear::reconstitute_from_base(inner_leaf);
        let leaf = unsafe { std::mem::transmute::<_, Vec<EF>>(leaf) };
        (leaf, proof)
    } else {
        unimplemented!()
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_verify<F: Field, EF: ExtensionField<F>>(
    merkle_root: [F; DIGEST_ELEMS],
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<[F; DIGEST_ELEMS]>,
) -> bool {
    let perm = default_koalabear_poseidon1_16();
    let log_max_height = utils::log2_strict_usize(dimension.height.next_power_of_two());
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [KoalaBear; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<QuinticExtensionFieldKB>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[KoalaBear; DIGEST_ELEMS]>>(proof) };
        let base_data = QuinticExtensionFieldKB::flatten_to_base(data);
        symetric::merkle::merkle_verify::<_, _, DIGEST_ELEMS, 16, 8>(
            &perm,
            &merkle_root,
            log_max_height,
            index,
            &base_data,
            proof,
        )
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let merkle_root = unsafe { std::mem::transmute_copy::<_, [KoalaBear; DIGEST_ELEMS]>(&merkle_root) };
        let data = unsafe { std::mem::transmute::<_, Vec<KoalaBear>>(data) };
        let proof = unsafe { std::mem::transmute::<_, &Vec<[KoalaBear; DIGEST_ELEMS]>>(proof) };
        let base_data = KoalaBear::flatten_to_base(data);
        symetric::merkle::merkle_verify::<_, _, DIGEST_ELEMS, 16, 8>(
            &perm,
            &merkle_root,
            log_max_height,
            index,
            &base_data,
            proof,
        )
    } else {
        unimplemented!()
    }
}

#[allow(clippy::missing_transmute_annotations)]
pub(crate) fn merkle_verify_sha2<F: Field + PrimeField32, EF: ExtensionField<F>>(
    merkle_root: Sha256Digest,
    index: usize,
    dimension: Dimensions,
    data: Vec<EF>,
    proof: &Vec<Sha256Digest>,
) -> bool {
    let log_max_height = utils::log2_strict_usize(dimension.height.next_power_of_two());
    if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, QuinticExtensionFieldKB)>() {
        let data = unsafe { std::mem::transmute::<_, Vec<QuinticExtensionFieldKB>>(data) };
        let base_data: Vec<KoalaBear> = QuinticExtensionFieldKB::flatten_to_base(data);
        sha2_merkle_verify(&merkle_root, log_max_height, index, &base_data, proof)
    } else if TypeId::of::<(F, EF)>() == TypeId::of::<(KoalaBear, KoalaBear)>() {
        let data = unsafe { std::mem::transmute::<_, Vec<KoalaBear>>(data) };
        let base_data = KoalaBear::flatten_to_base(data);
        sha2_merkle_verify(&merkle_root, log_max_height, index, &base_data, proof)
    } else {
        unimplemented!()
    }
}

#[derive(Debug, Clone)]
pub struct WhirMerkleTree<F, M, const DIGEST_ELEMS: usize> {
    pub(crate) leaf: M,
    pub(crate) tree: symetric::merkle::MerkleTree<F, DIGEST_ELEMS>,
    full_leaf_base_width: usize,
}

#[derive(Debug, Clone)]
pub struct WhirMerkleTreeSha2<F: PrimeField32, M: Matrix<F>> {
    pub(crate) leaf: M,
    pub(crate) tree: MerkleTreeSha2,
    full_leaf_base_width: usize,
    _marker: std::marker::PhantomData<F>,
}

impl<F: Clone + Copy + Default + Send + Sync, M: Matrix<F>, const DIGEST_ELEMS: usize>
    WhirMerkleTree<F, M, DIGEST_ELEMS>
{
    #[instrument(name = "build merkle tree", skip_all)]
    pub fn new<P, Perm, const WIDTH: usize, const RATE: usize>(
        perm: &Perm,
        leaf: M,
        full_leaf_base_width: usize,
        effective_base_width: usize,
    ) -> Self
    where
        P: PackedValue<Value = F> + Default,
        Perm: Compression<[F; WIDTH]> + Compression<[P; WIDTH]>,
    {
        let n_zero_suffix_rate_chunks = (full_leaf_base_width - effective_base_width) / RATE;
        let first_layer = if n_zero_suffix_rate_chunks >= 2 {
            let scalar_state = symetric::precompute_zero_suffix_state::<F, Perm, WIDTH, RATE, DIGEST_ELEMS>(
                perm,
                n_zero_suffix_rate_chunks,
            );
            let packed_state: [P; WIDTH] = std::array::from_fn(|i| P::from_fn(|_| scalar_state[i]));
            first_digest_layer_with_initial_state::<P, Perm, _, DIGEST_ELEMS, WIDTH, RATE>(
                perm,
                &leaf,
                &packed_state,
                effective_base_width,
            )
        } else {
            first_digest_layer::<P, Perm, _, DIGEST_ELEMS, WIDTH, RATE>(perm, &leaf, full_leaf_base_width)
        };
        let tree = symetric::merkle::MerkleTree::from_first_layer::<P, Perm, WIDTH>(perm, first_layer);
        Self {
            leaf,
            tree,
            full_leaf_base_width,
        }
    }

    #[must_use]
    pub fn root(&self) -> [F; DIGEST_ELEMS] {
        self.tree.root()
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<[F; DIGEST_ELEMS]>) {
        let log_height = log2_ceil_usize(self.leaf.height());
        let mut opening: Vec<F> = self.leaf.row(index).unwrap().into_iter().collect();
        opening.resize(self.full_leaf_base_width, F::default());
        let proof = self.tree.open_siblings(index, log_height);
        (opening, proof)
    }
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn first_digest_layer<P, Perm, M, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    matrix: &M,
    full_width: usize,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Perm: Compression<[P::Value; WIDTH]> + Compression<[P; WIDTH]>,
    M: Matrix<P::Value>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let matrix_width = matrix.width();
    let n_trailing_zeros = full_width - matrix_width;

    let mut digests = unsafe { uninitialized_vec(height) };

    digests
        .par_chunks_exact_mut(width)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row = i * width;
            let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, matrix_width, n_trailing_zeros);
            let packed_digest: [P; DIGEST_ELEMS] =
                symetric::hash_rtl_iter::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(perm, rtl_iter);
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    digests
}

#[instrument(skip_all)]
fn first_digest_layer_with_initial_state<P, Perm, M, const DIGEST_ELEMS: usize, const WIDTH: usize, const RATE: usize>(
    perm: &Perm,
    matrix: &M,
    packed_initial_state: &[P; WIDTH],
    effective_base_width: usize,
) -> Vec<[P::Value; DIGEST_ELEMS]>
where
    P: PackedValue + Default,
    P::Value: Default + Copy,
    Perm: Compression<[P::Value; WIDTH]> + Compression<[P; WIDTH]>,
    M: Matrix<P::Value>,
{
    let width = P::WIDTH;
    let height = matrix.height();
    assert!(height.is_multiple_of(width));
    let n_pad = (RATE - effective_base_width % RATE) % RATE;

    let mut digests = unsafe { uninitialized_vec(height) };

    digests
        .par_chunks_exact_mut(width)
        .enumerate()
        .for_each(|(i, digests_chunk)| {
            let first_row = i * width;
            let rtl_iter = matrix.vertically_packed_row_rtl::<P>(first_row, effective_base_width, n_pad);
            let packed_digest: [P; DIGEST_ELEMS] =
                symetric::hash_rtl_iter_with_initial_state::<_, _, _, WIDTH, RATE, DIGEST_ELEMS>(
                    perm,
                    rtl_iter,
                    packed_initial_state,
                );
            for (dst, src) in digests_chunk.iter_mut().zip(unpack_array(packed_digest)) {
                *dst = src;
            }
        });

    digests
}

#[instrument(name = "first digest layer", level = "debug", skip_all)]
fn sha2_first_digest_layer<F, M>(h: &Sha256, matrix: &M, full_width: usize) -> Vec<Sha256Digest>
where
    F: PrimeField32,
    M: Matrix<F>,
{
    let height = matrix.height();
    let matrix_width = matrix.width();
    let n_trailing_zeros = full_width - matrix_width;

    (0..height)
        .into_par_iter()
        .map(|r| {
            let mut hasher = h.clone();
            for value in matrix.row(r).unwrap() {
                hasher.update(value.as_canonical_u32().to_le_bytes());
            }
            for _ in 0..n_trailing_zeros {
                hasher.update(F::ZERO.as_canonical_u32().to_le_bytes());
            }
            let digest = hasher.finalize();
            digest[..16].try_into().unwrap()
        })
        .collect()
}

fn sha2_compress_pair(left: &Sha256Digest, right: &Sha256Digest) -> Sha256Digest {
    let mut hasher = Sha256::new();
    hasher.update(left);
    hasher.update(right);
    let digest = hasher.finalize();
    digest[..16].try_into().unwrap()
}

fn sha2_merkle_verify<F: PrimeField32>(
    commit: &Sha256Digest,
    log_height: usize,
    mut index: usize,
    opened_values: &[F],
    opening_proof: &[Sha256Digest],
) -> bool {
    if opening_proof.len() != log_height {
        return false;
    }

    let mut hasher = Sha256::new();
    for value in opened_values {
        hasher.update(value.as_canonical_u32().to_le_bytes());
    }
    let digest = hasher.finalize();
    let mut root: Sha256Digest = digest[..16].try_into().unwrap();

    for sibling in opening_proof {
        let (left, right) = if index & 1 == 0 {
            (root, *sibling)
        } else {
            (*sibling, root)
        };
        root = sha2_compress_pair(&left, &right);
        index >>= 1;
    }

    commit == &root
}

impl<F: PrimeField32, M: Matrix<F>> WhirMerkleTreeSha2<F, M> {
    #[instrument(name = "build merkle tree", skip_all)]
    pub fn new(leaf: M, full_leaf_base_width: usize, effective_base_width: usize) -> Self {
        assert!(leaf.height().is_power_of_two());
        assert!(leaf.width() <= full_leaf_base_width);
        assert!(effective_base_width <= full_leaf_base_width);

        let first_layer = sha2_first_digest_layer(&Sha256::new(), &leaf, full_leaf_base_width);
        let mut digest_layers = vec![first_layer];

        tracing::debug_span!("asc").in_scope(|| {
            while digest_layers.last().unwrap().len() > 1 {
                let prev_layer = digest_layers.last().unwrap();
                assert!(prev_layer.len().is_multiple_of(2));
                let next_layer = prev_layer
                    .par_chunks_exact(2)
                    .map(|pair| sha2_compress_pair(&pair[0], &pair[1]))
                    .collect();
                digest_layers.push(next_layer);
            }
        });

        let tree = MerkleTreeSha2 { digest_layers };
        Self {
            leaf,
            tree,
            full_leaf_base_width,
            _marker: std::marker::PhantomData,
        }
    }

    #[must_use]
    pub fn root(&self) -> Sha256Digest {
        self.tree.root()
    }

    pub fn open(&self, index: usize) -> (Vec<F>, Vec<Sha256Digest>) {
        let log_height = log2_ceil_usize(self.leaf.height());
        let mut opening: Vec<F> = self.leaf.row(index).unwrap().into_iter().collect();
        opening.resize(self.full_leaf_base_width, F::default());
        let proof = self.tree.open_siblings(index, log_height);
        (opening, proof)
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use field::integers::QuotientMap;

    use super::*;

    fn pseudo_random_koalabear(index: usize) -> KoalaBear {
        let mut x = index as u64;
        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        KoalaBear::from_int(x ^ (x >> 31))
    }

    #[test]
    fn whir_sha2_merkle_tree_builds_expected_layers() {
        let width = 8;
        let height = 4;
        let values: Vec<_> = (0..width * height).map(pseudo_random_koalabear).collect();
        let matrix = DenseMatrix::new(values, width);

        let (root, tree) = merkle_commit_sha2::<KoalaBear, KoalaBear>(matrix, width, width);

        assert_eq!(tree.tree.digest_layers.len(), log2_ceil_usize(height) + 1);
        assert_eq!(tree.tree.digest_layers[0].len(), height);
        assert_eq!(tree.tree.digest_layers[1].len(), height / 2);
        assert_eq!(tree.tree.digest_layers[2].len(), 1);
        assert_eq!(tree.root(), root);
    }

    #[test]
    fn whir_sha2_merkle_opening_verifies() {
        let width = 8;
        let height = 4;
        let index = 2;
        let values: Vec<_> = (0..width * height).map(pseudo_random_koalabear).collect();
        let matrix = DenseMatrix::new(values, width);

        let (root, tree) = merkle_commit_sha2::<KoalaBear, KoalaBear>(matrix, width, width);
        let (leaf, proof) = merkle_open_sha2::<KoalaBear, KoalaBear>(&tree, index);

        assert!(merkle_verify_sha2::<KoalaBear, KoalaBear>(
            root,
            index,
            Dimensions { width, height },
            leaf,
            &proof,
        ));
    }

    use tracing_forest::{ForestLayer, util::LevelFilter};
    use tracing_subscriber::{EnvFilter, Registry, layer::SubscriberExt, util::SubscriberInitExt};

    pub fn init_tracing() {
        let env_filter = EnvFilter::builder()
            .with_default_directive(LevelFilter::INFO.into())
            .from_env_lossy();

        let _ = Registry::default()
            .with(env_filter)
            .with(ForestLayer::default())
            .try_init();
    }

    #[test]
    fn bench_merkle_commit_koalabear_width_32_log_sizes() {
        let folding_factor = 7;
        let width = 1usize << folding_factor;

        init_tracing();

        for log_size in 20..=26 {
            let n_values = 1usize << log_size;
            let height = n_values / width;
            let values: Vec<_> = (0..n_values).map(pseudo_random_koalabear).collect();
            let matrix = DenseMatrix::new(values, width);

            assert_eq!(matrix.width(), width);
            assert_eq!(matrix.height(), height);

            let start = Instant::now();
            let (_root, prover_data) = merkle_commit::<KoalaBear, KoalaBear>(matrix, width, width);
            let elapsed = start.elapsed();

            assert_eq!(prover_data.leaf.width(), width);
            assert_eq!(prover_data.leaf.height(), height);
            assert_eq!(prover_data.full_leaf_base_width, width);

            let log_height = log2_ceil_usize(height);
            println!("poseidon log_size={log_size}, log_height={log_height}, width={width}, time={elapsed:?}",);
        }
    }

    #[test]
    fn bench_sha256_merkle_commit_koalabear_width_32_log_sizes() {
        let folding_factor = 7;
        let width = 1usize << folding_factor;

        init_tracing();

        for log_size in 20..=26 {
            let n_values = 1usize << log_size;
            let height = n_values / width;
            let values: Vec<_> = (0..n_values).map(pseudo_random_koalabear).collect();
            let matrix = DenseMatrix::new(values, width);

            assert_eq!(matrix.width(), width);
            assert_eq!(matrix.height(), height);

            let start = Instant::now();
            let (root, tree) = merkle_commit_sha2::<KoalaBear, KoalaBear>(matrix, width, width);
            let elapsed = start.elapsed();

            assert_eq!(tree.tree.digest_layers[0].len(), height);
            assert_eq!(tree.tree.digest_layers.last().unwrap()[0], root);

            let log_height = log2_ceil_usize(height);
            println!("sha256 log={log_size}, log_height={log_height}, width={width}, time={elapsed:?}",);
        }
    }
}
