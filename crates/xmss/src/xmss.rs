use multilinear_toolkit::prelude::*;
use rand::{CryptoRng, Rng, SeedableRng, rngs::StdRng};
use sha3::{Digest as Sha3Digest, Keccak256};
use utils::poseidon16_compress_pair;

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) start: u32,
    pub(crate) end: u32,
    pub(crate) seed: [u8; 32],
    // merkle_tree[level] stores nodes at that level whose subtree overlaps [start, end].
    // At level l, stored indices go from (start >> l) to (end >> l).
    pub(crate) merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub slot: u32,
    pub merkle_proof: Vec<Digest>,
}

#[derive(Debug, Clone)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: u64) -> WotsSecretKey {
    let mut hasher = Keccak256::new();
    hasher.update(b"wots_secret_key");
    hasher.update(seed);
    hasher.update(slot.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    WotsSecretKey::random(&mut rng)
}

/// Deterministic pseudo-random digest for an out-of-range tree node.
fn gen_random_node(seed: &[u8; 32], level: usize, index: u64) -> Digest {
    let mut hasher = Keccak256::new();
    hasher.update(b"random_node");
    hasher.update(seed);
    hasher.update((level as u64).to_le_bytes());
    hasher.update(index.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    rng.random()
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    InvalidRange,
}

pub fn xmss_key_gen(seed: [u8; 32], start: u32, end: u32) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if start > end || end as u64 >= (1 << LOG_LIFETIME) {
        return Err(XmssKeyGenError::InvalidRange);
    }
    // Level 0: WOTS leaf hashes for slots in [start, end]
    let leaves: Vec<Digest> = (start as u64..end as u64 + 1)
        .into_par_iter()
        .map(|slot| {
            let wots = gen_wots_secret_key(&seed, slot);
            wots.public_key().hash()
        })
        .collect();
    let mut merkle_tree = vec![leaves];
    // Build levels 1..=LOG_LIFETIME.
    // At level l, we store nodes with index in [(start >> l), (end >> l)].
    // Children outside [start, end]'s subtree are replaced by gen_random_node.
    for level in 1..=LOG_LIFETIME {
        let base: u64 = (start as u64) >> level;
        let top: u64 = (end as u64) >> level;
        let prev_base: u64 = (start as u64) >> (level - 1);
        let prev_top: u64 = (end as u64) >> (level - 1);
        let nodes: Vec<Digest> = {
            let prev = &merkle_tree[level - 1];
            (base..top + 1)
                .into_par_iter()
                .map(|i| {
                    let left_idx = 2 * i;
                    let right_idx = 2 * i + 1;
                    let left = if left_idx >= prev_base && left_idx <= prev_top {
                        prev[(left_idx - prev_base) as usize]
                    } else {
                        gen_random_node(&seed, level - 1, left_idx)
                    };
                    let right = if right_idx >= prev_base && right_idx <= prev_top {
                        prev[(right_idx - prev_base) as usize]
                    } else {
                        gen_random_node(&seed, level - 1, right_idx)
                    };
                    poseidon16_compress_pair(left, right)
                })
                .collect()
        };
        merkle_tree.push(nodes);
    }
    let pub_key = XmssPublicKey {
        merkle_root: merkle_tree.last().unwrap()[0],
    };
    let secret_key = XmssSecretKey {
        start,
        end,
        seed,
        merkle_tree,
    };
    Ok((secret_key, pub_key))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssSignatureError {
    SlotOutOfRange,
}

pub fn xmss_sign<R: CryptoRng>(
    rng: &mut R,
    secret_key: &XmssSecretKey,
    message_hash: &[F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<XmssSignature, XmssSignatureError> {
    if slot < secret_key.start || slot > secret_key.end {
        return Err(XmssSignatureError::SlotOutOfRange);
    }
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot as u64);
    let merkle_root = secret_key.public_key().merkle_root;
    let truncated_merkle_root = merkle_root[0..TRUNCATED_MERKLE_ROOT_LEN_FE].try_into().unwrap();
    let wots_signature = wots_secret_key.sign(message_hash, slot, &truncated_merkle_root, rng);
    let merkle_proof = (0..LOG_LIFETIME)
        .map(|level| {
            let neighbour_index = ((slot as u64) >> level) ^ 1;
            let base = (secret_key.start as u64) >> level;
            let top = (secret_key.end as u64) >> level;
            if neighbour_index >= base && neighbour_index <= top {
                secret_key.merkle_tree[level][(neighbour_index - base) as usize]
            } else {
                gen_random_node(&secret_key.seed, level, neighbour_index)
            }
        })
        .collect();
    Ok(XmssSignature {
        wots_signature,
        slot,
        merkle_proof,
    })
}

impl XmssSecretKey {
    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            merkle_root: self.merkle_tree.last().unwrap()[0],
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssVerifyError {
    InvalidWots,
    InvalidMerklePath,
}

pub fn xmss_verify(
    pub_key: &XmssPublicKey,
    message: &[F; MESSAGE_LEN_FE],
    signature: &XmssSignature,
) -> Result<(), XmssVerifyError> {
    xmss_verify_with_poseidon_trace(pub_key, message, signature).map(|_| ())
}

pub fn xmss_verify_with_poseidon_trace(
    pub_key: &XmssPublicKey,
    message: &[F; MESSAGE_LEN_FE],
    signature: &XmssSignature,
) -> Result<Poseidon16History, XmssVerifyError> {
    let mut poseidon_16_trace = Vec::new();
    let truncated_merkle_root = pub_key.merkle_root[0..TRUNCATED_MERKLE_ROOT_LEN_FE].try_into().unwrap();
    let wots_public_key = signature
        .wots_signature
        .recover_public_key_with_poseidon_trace(
            message,
            signature.slot,
            &truncated_merkle_root,
            &signature.wots_signature,
            &mut poseidon_16_trace,
        )
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current_hash = wots_public_key.hash_with_poseidon_trace(&mut poseidon_16_trace);
    if signature.merkle_proof.len() != LOG_LIFETIME {
        return Err(XmssVerifyError::InvalidMerklePath);
    }
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = (((signature.slot as u64) >> level) & 1) == 0;
        if is_left {
            current_hash = poseidon16_compress_with_trace(&current_hash, neighbour, &mut poseidon_16_trace);
        } else {
            current_hash = poseidon16_compress_with_trace(neighbour, &current_hash, &mut poseidon_16_trace);
        }
    }
    if current_hash == pub_key.merkle_root {
        Ok(poseidon_16_trace)
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
