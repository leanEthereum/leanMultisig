use backend::*;
use rand::{CryptoRng, RngExt, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};
use sha3::{Digest as Sha3Digest, Keccak256};
use utils::poseidon16_compress;

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) slot_start: u32, // inclusive
    pub(crate) slot_end: u32,   // inclusive
    pub(crate) public_param: PublicParam,
    pub(crate) seed: [u8; 32],
    // At level l, stored indices go from (slot_start >> l) to (slot_end >> l).
    pub(crate) merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub merkle_proof: Vec<Digest>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub public_param: PublicParam,
}

impl XmssPublicKey {
    pub fn flaten(&self) -> [F; PUB_KEY_FLAT_SIZE] {
        let mut output = [F::default(); PUB_KEY_FLAT_SIZE];
        output[..XMSS_DIGEST_LEN].copy_from_slice(&self.merkle_root);
        output[XMSS_DIGEST_LEN..].copy_from_slice(&self.public_param);
        output
    }
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: u32, public_param: PublicParam) -> WotsSecretKey {
    let mut hasher = Keccak256::new();
    hasher.update(b"wots_secret_key");
    hasher.update(seed);
    hasher.update(slot.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    WotsSecretKey::random(&mut rng, public_param, slot)
}

fn gen_public_param(seed: &[u8; 32]) -> PublicParam {
    let mut hasher = Keccak256::new();
    hasher.update(b"public_param");
    hasher.update(seed);
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    rng.random()
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

pub fn xmss_key_gen(
    seed: [u8; 32],
    slot_start: u32,
    slot_end: u32,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if slot_start > slot_end || slot_end as u64 >= (1 << LOG_LIFETIME) {
        return Err(XmssKeyGenError::InvalidRange);
    }
    let public_param: PublicParam = gen_public_param(&seed);
    // Level 0: WOTS leaf hashes for slots in [slot_start, slot_end]
    let leaves: Vec<Digest> = (slot_start..=slot_end)
        .into_par_iter()
        .map(|slot| {
            let wots = gen_wots_secret_key(&seed, slot, public_param);
            wots.public_key().hash(public_param, slot)
        })
        .collect();
    let mut merkle_tree = vec![leaves];
    // Build levels 1..=LOG_LIFETIME.
    // At level l, we store nodes with index in [(slot_start >> l), (slot_end >> l)].
    // Children outside [slot_start, slot_end]'s subtree are replaced by gen_random_node.
    for level in 1..=LOG_LIFETIME {
        let base: u64 = (slot_start as u64) >> level;
        let top: u64 = (slot_end as u64) >> level;
        let prev_base: u64 = (slot_start as u64) >> (level - 1);
        let prev_top: u64 = (slot_end as u64) >> (level - 1);
        let nodes: Vec<Digest> = {
            let prev = &merkle_tree[level - 1];
            (base..=top)
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
                    let merkle_data = build_merkle_data(
                        make_tweak(TWEAK_TYPE_MERKLE, level, i as u32),
                        &public_param,
                        &left,
                        &right,
                    );
                    poseidon16_compress(merkle_data)[..XMSS_DIGEST_LEN].try_into().unwrap()
                })
                .collect()
        };
        merkle_tree.push(nodes);
    }
    let pub_key = XmssPublicKey {
        merkle_root: merkle_tree.last().unwrap()[0],
        public_param,
    };
    let secret_key = XmssSecretKey {
        slot_start,
        slot_end,
        public_param,
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
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
) -> Result<XmssSignature, XmssSignatureError> {
    let (randomness, _, _) = find_randomness_for_wots_encoding(message, slot, &secret_key.public_key(), rng);
    xmss_sign_with_randomness(secret_key, message, slot, randomness)
}

pub fn xmss_sign_with_randomness(
    secret_key: &XmssSecretKey,
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    randomness: [F; RANDOMNESS_LEN_FE],
) -> Result<XmssSignature, XmssSignatureError> {
    if slot < secret_key.slot_start || slot > secret_key.slot_end {
        return Err(XmssSignatureError::SlotOutOfRange);
    }
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot, secret_key.public_param);
    let wots_signature = wots_secret_key.sign_with_randomness(message, slot, &secret_key.public_key(), randomness);
    let merkle_proof = (0..LOG_LIFETIME)
        .map(|level| {
            let neighbour_index = ((slot as u64) >> level) ^ 1;
            let base = (secret_key.slot_start as u64) >> level;
            let top = (secret_key.slot_end as u64) >> level;
            if neighbour_index >= base && neighbour_index <= top {
                secret_key.merkle_tree[level][(neighbour_index - base) as usize]
            } else {
                gen_random_node(&secret_key.seed, level, neighbour_index)
            }
        })
        .collect();
    Ok(XmssSignature {
        wots_signature,
        merkle_proof,
    })
}

impl XmssSecretKey {
    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            merkle_root: self.merkle_tree.last().unwrap()[0],
            public_param: self.public_param,
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
    slot: u32,
) -> Result<(), XmssVerifyError> {
    let wots_public_key = signature
        .wots_signature
        .recover_public_key(message, slot, pub_key, &signature.wots_signature)
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current_hash = wots_public_key.hash(pub_key.public_param, slot);
    if signature.merkle_proof.len() != LOG_LIFETIME {
        return Err(XmssVerifyError::InvalidMerklePath);
    }
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = (((slot as u64) >> level) & 1) == 0;
        let parent_index = ((slot as u64) >> (level + 1)) as u32;
        let (left_child, right_child) = if is_left {
            (current_hash, *neighbour)
        } else {
            (*neighbour, current_hash)
        };
        let merkle_data = build_merkle_data(
            make_tweak(TWEAK_TYPE_MERKLE, level + 1, parent_index),
            &pub_key.public_param,
            &left_child,
            &right_child,
        );
        current_hash = poseidon16_compress(merkle_data)[..XMSS_DIGEST_LEN].try_into().unwrap();
    }
    if current_hash == pub_key.merkle_root {
        Ok(())
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
