use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use sha3::{Digest as Sha3Digest, Keccak256};

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub first_slot: usize,
    pub seed: [u8; 32],
    pub merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub slot: usize, // unused for now (Toy XMSS)
    pub merkle_proof: Vec<Digest>,
}

#[derive(Debug)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub first_slot: usize,
    pub log_lifetime: usize,
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: usize) -> WotsSecretKey {
    let mut hasher = Keccak256::new();
    hasher.update(seed);
    hasher.update(&slot.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    WotsSecretKey::random(&mut rng)
}
impl XmssSecretKey {
    pub fn new(seed: [u8; 32], first_slot: usize, log_lifetime: usize) -> Self {
        let leaves = (first_slot..first_slot + (1 << log_lifetime))
            .into_par_iter()
            .map(|slot| {
                let wots = gen_wots_secret_key(&seed, slot);
                wots.public_key().hash()
            })
            .collect::<Vec<_>>();
        let mut merkle_tree = vec![leaves];
        for _ in 0..log_lifetime {
            merkle_tree.push(
                merkle_tree
                    .last()
                    .unwrap()
                    .par_chunks(2)
                    .map(|chunk| poseidon16_compress(&chunk[0], &chunk[1]))
                    .collect(),
            );
        }
        Self {
            first_slot,
            seed,
            merkle_tree,
        }
    }

    pub fn log_lifetime(&self) -> usize {
        self.merkle_tree.len() - 1
    }

    pub fn lifetime(&self) -> usize {
        1 << self.log_lifetime()
    }

    pub fn sign(&self, message_hash: &Digest, slot: usize, rng: &mut impl Rng) -> Option<XmssSignature> {
        if slot < self.first_slot {
            return None;
        }
        let wots_index = slot - self.first_slot;
        if wots_index >= self.lifetime() {
            return None;
        }
        let wots_secret_key = gen_wots_secret_key(&self.seed, slot);
        let wots_signature = wots_secret_key.sign(message_hash, rng);
        let merkle_proof = (0..self.log_lifetime())
            .scan(wots_index, |current_idx, level| {
                let neighbour_index = *current_idx ^ 1;
                let neighbour = self.merkle_tree[level][neighbour_index];
                // Move up to the next level.
                *current_idx /= 2;
                Some(neighbour)
            })
            .collect();
        Some(XmssSignature {
            wots_signature,
            slot,
            merkle_proof,
        })
    }

    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            first_slot: self.first_slot,
            merkle_root: self.merkle_tree.last().unwrap()[0],
            log_lifetime: self.log_lifetime(),
        }
    }
}

impl XmssPublicKey {
    pub fn verify(&self, message_hash: &Digest, signature: &XmssSignature) -> Option<()> {
        self.verify_with_poseidon_trace(message_hash, signature).map(|_| ())
    }

    pub fn verify_with_poseidon_trace(
        &self,
        message_hash: &Digest,
        signature: &XmssSignature,
    ) -> Option<(Poseidon16History, Poseidon24History)> {
        if signature.slot < self.first_slot {
            return None;
        }
        let wots_index = signature.slot - self.first_slot;
        if wots_index >= (1 << self.log_lifetime) {
            return None;
        }
        let mut poseidon_16_trace = Vec::new();
        let mut poseidon_24_trace = Vec::new();
        let wots_public_key = signature.wots_signature.recover_public_key_with_poseidon_trace(
            message_hash,
            &signature.wots_signature,
            &mut poseidon_16_trace,
        )?;
        // merkle root verification
        let mut current_hash = wots_public_key.hash_with_poseidon_trace(&mut poseidon_24_trace);
        if signature.merkle_proof.len() != self.log_lifetime {
            return None;
        }
        for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
            let is_left = ((wots_index >> level) & 1) == 0;
            if is_left {
                current_hash = poseidon16_compress_with_trace(&current_hash, neighbour, &mut poseidon_16_trace)
            } else {
                current_hash = poseidon16_compress_with_trace(neighbour, &current_hash, &mut poseidon_16_trace);
            }
        }
        if current_hash == self.merkle_root {
            Some((poseidon_16_trace, poseidon_24_trace))
        } else {
            None
        }
    }
}
