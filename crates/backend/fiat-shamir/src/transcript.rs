use field::Field;
use serde::{Deserialize, Serialize};

use crate::PrunedMerklePaths;

pub const DIGEST_LEN_FE: usize = 8;

#[derive(Debug, Clone)]
pub struct MerkleOpening<F> {
    pub leaf_data: Vec<F>,
    pub path: Vec<[F; DIGEST_LEN_FE]>,
}

/// "RawProof": the format which is used in the zkVM recursion program (no Merkle pruning, no sumcheck optimization to send less data, etc)
#[derive(Clone)]
pub struct RawProof<F> {
    pub transcript: Vec<F>,
    pub merkle_openings: Vec<MerkleOpening<F>>,
}

#[derive(Debug, Clone)]
pub struct MerklePath<Data, F> {
    pub leaf_data: Vec<Data>,
    pub sibling_hashes: Vec<[F; DIGEST_LEN_FE]>,
    // does not appear in the proof itself, but useful for Merkle pruning
    pub leaf_index: usize,
}

#[derive(Debug, Clone)]
pub struct MerklePaths<Data, F>(pub(crate) Vec<MerklePath<Data, F>>);

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Proof<F> {
    pub(crate) transcript: Vec<F>,
    pub(crate) merkle_paths: Vec<PrunedMerklePaths<F, F>>,
}

impl<F: Field> Proof<F> {
    pub fn proof_size_fe(&self) -> usize {
        let merkle_size: usize = self
            .merkle_paths
            .iter()
            .map(|paths| {
                paths.leaf_data.iter().map(|d| d.len()).sum::<usize>()
                    + paths
                        .paths
                        .iter()
                        .map(|(_, sh): &(_, Vec<_>)| sh.len() * DIGEST_LEN_FE)
                        .sum::<usize>()
            })
            .sum();
        self.transcript.len() + merkle_size
    }
}
