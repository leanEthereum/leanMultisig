use std::{any::TypeId, iter::repeat_n};

use field::Field;
use koala_bear::{KoalaBear, default_koalabear_poseidon2_16};
use serde::{Deserialize, Serialize};

use crate::{PrunedMerklePaths, challenger::RATE};

pub(crate) const DIGEST_LEN_FE: usize = 8;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TranscriptData<F, MerklePaths> {
    Interraction(Vec<F>),
    GrindingWitness(F),
    MerklePaths(MerklePaths),
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

#[derive(Debug, Clone)]
pub struct Proof<F>(pub(crate) Vec<TranscriptData<F, MerklePaths<F, F>>>);

impl<F: Field> Proof<F> {
    pub fn raw_proof(&self) -> Vec<F> {
        let mut proof = Vec::new();
        for item in &self.0 {
            match item {
                TranscriptData::Interraction(scalars) => {
                    proof.extend_from_slice(scalars);
                    let padding = scalars.len().next_multiple_of(RATE) - scalars.len();
                    proof.extend(repeat_n(F::ZERO, padding));
                }
                TranscriptData::GrindingWitness(scalar) => {
                    proof.push(*scalar);
                    proof.extend(repeat_n(F::ZERO, RATE - 1));
                }
                TranscriptData::MerklePaths(paths) => {
                    for path in &paths.0 {
                        proof.extend_from_slice(&path.leaf_data);
                        assert!(path.leaf_data.len() % RATE == 0);
                    }
                    for path in &paths.0 {
                        for hash in &path.sibling_hashes {
                            proof.extend_from_slice(hash);
                        }
                    }
                }
            }
        }
        proof
    }
    pub fn prune(self) -> PrunedProof<F> {
        PrunedProof(
            self.0
                .into_iter()
                .map(|item| match item {
                    TranscriptData::Interraction(scalars) => TranscriptData::Interraction(scalars),
                    TranscriptData::GrindingWitness(scalar) => TranscriptData::GrindingWitness(scalar),
                    TranscriptData::MerklePaths(paths) => TranscriptData::MerklePaths(paths.prune()),
                })
                .collect(),
        )
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrunedProof<F>(pub(crate) Vec<TranscriptData<F, PrunedMerklePaths<F, F>>>);

impl<F: Field> PrunedProof<F> {
    pub fn restore(self) -> Option<Proof<F>> {
        Some(Proof(
            self.0
                .into_iter()
                .map(|item| {
                    Some(match item {
                        TranscriptData::Interraction(scalars) => TranscriptData::Interraction(scalars),
                        TranscriptData::GrindingWitness(scalar) => TranscriptData::GrindingWitness(scalar),
                        TranscriptData::MerklePaths(paths) => {
                            if TypeId::of::<F>() == TypeId::of::<KoalaBear>() {
                                // TODO avoid ugly unsafe
                                let paths: PrunedMerklePaths<KoalaBear, KoalaBear> =
                                    unsafe { std::mem::transmute(paths) };
                                let perm = default_koalabear_poseidon2_16();
                                let hash_fn = |data: &[KoalaBear]| {
                                    symetric::hash_slice::<_, _, 16, 8, DIGEST_LEN_FE>(&perm, data)
                                };
                                let combine_fn =
                                    |left: &[KoalaBear; DIGEST_LEN_FE], right: &[KoalaBear; DIGEST_LEN_FE]| {
                                        symetric::compress(&perm, [*left, *right])
                                    };
                                let restored = paths.restore(&hash_fn, &combine_fn)?;

                                TranscriptData::MerklePaths(unsafe {
                                    std::mem::transmute::<MerklePaths<KoalaBear, KoalaBear>, MerklePaths<F, F>>(
                                        restored,
                                    )
                                })
                            } else {
                                unimplemented!()
                            }
                        }
                    })
                })
                .collect::<Option<Vec<_>>>()?,
        ))
    }

    pub fn proof_size_fe(&self) -> usize {
        // We don't count the various metadata (like number of merkle paths, lengths, etc.) because it can de deduced from the transcript itself.
        let mut size = 0;
        for item in &self.0 {
            match item {
                TranscriptData::Interraction(scalars) => {
                    size += scalars.len();
                }
                TranscriptData::GrindingWitness(_) => {
                    size += 1;
                }
                TranscriptData::MerklePaths(paths) => {
                    for leaf_data in &paths.leaf_data {
                        size += leaf_data.len();
                    }
                    for (_, sibling_hashes) in &paths.paths {
                        size += sibling_hashes.len() * DIGEST_LEN_FE;
                    }
                }
            }
        }
        size
    }
}
