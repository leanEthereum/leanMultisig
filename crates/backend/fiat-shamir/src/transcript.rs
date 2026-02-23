use std::{any::TypeId, iter::repeat_n};

use field::Field;
use koala_bear::{KoalaBear, default_koalabear_poseidon2_16};
use serde::{Deserialize, Serialize};

use crate::{PrunedMerklePaths, challenger::RATE};

pub(crate) const DIGEST_LEN_FE: usize = 8;

#[derive(Debug, Clone)]
pub struct MerkleOpening<F> {
    pub leaf_data: Vec<F>,
    pub path: Vec<[F; DIGEST_LEN_FE]>,
}

#[derive(Clone)]
pub struct RawProof<F> {
    pub transcript: Vec<F>,
    pub merkle_openings: Vec<MerkleOpening<F>>,
}

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
    pub fn into_raw_proof(self) -> RawProof<F> {
        let mut transcript = Vec::new();
        let mut merkle_openings = Vec::new();
        for item in self.0 {
            match item {
                TranscriptData::Interraction(scalars) => {
                    let padding = scalars.len().next_multiple_of(RATE) - scalars.len();
                    transcript.extend(scalars);
                    transcript.extend(repeat_n(F::ZERO, padding));
                }
                TranscriptData::GrindingWitness(scalar) => {
                    transcript.push(scalar);
                    transcript.extend(repeat_n(F::ZERO, RATE - 1));
                }
                TranscriptData::MerklePaths(paths) => {
                    for path in paths.0 {
                        assert!(path.leaf_data.len() % RATE == 0);
                        merkle_openings.push(MerkleOpening {
                            leaf_data: path.leaf_data,
                            path: path.sibling_hashes,
                        });
                    }
                }
            }
        }
        RawProof {
            transcript,
            merkle_openings,
        }
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
