use backend::*;
use rand::{CryptoRng, RngExt, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) slot_start: u32, // inclusive
    pub(crate) slot_end: u32,   // inclusive
    pub(crate) seed: [u8; 20],
    pub(crate) public_param: PublicParam,
    // At level l, stored indices go from (slot_start >> l) to (slot_end >> l).
    pub(crate) merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub slot: u32,
    pub merkle_proof: Vec<Digest>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub public_param: PublicParam,
}

/// Derive the public parameter deterministically from the seed.
fn gen_public_param(seed: &[u8; 20]) -> PublicParam {
    let mut rng_seed = [0u8; 32];
    rng_seed[..20].copy_from_slice(seed);
    rng_seed[20] = 0x02; // domain separator (0x00 = WOTS key, 0x01 = random node)
    let mut rng = StdRng::from_seed(rng_seed);
    rng.random()
}

fn gen_wots_secret_key(seed: &[u8; 20], slot: u32, public_param: &PublicParam) -> WotsSecretKey {
    let mut rng_seed = [0u8; 32];
    rng_seed[..20].copy_from_slice(seed);
    rng_seed[20] = 0x00;
    rng_seed[21..25].copy_from_slice(&slot.to_le_bytes());
    let mut rng = StdRng::from_seed(rng_seed);
    WotsSecretKey::random(&mut rng, public_param, slot)
}

/// Deterministic pseudo-random digest for an out-of-range tree node.
fn gen_random_node(seed: &[u8; 20], level: usize, index: u32) -> Digest {
    let mut rng_seed = [0u8; 32];
    rng_seed[..20].copy_from_slice(seed);
    rng_seed[20] = 0x01;
    rng_seed[21] = level as u8;
    rng_seed[22..26].copy_from_slice(&index.to_le_bytes());
    let mut rng = StdRng::from_seed(rng_seed);
    rng.random()
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    InvalidRange,
}

pub fn xmss_key_gen(
    seed: [u8; 20],
    slot_start: u32,
    slot_end: u32,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if slot_start > slot_end {
        return Err(XmssKeyGenError::InvalidRange);
    }
    let public_param = gen_public_param(&seed);

    // Level 0: WOTS leaf hashes for slots in [slot_start, slot_end]
    let leaves: Vec<Digest> = (slot_start..=slot_end)
        .into_par_iter()
        .map(|slot| {
            let wots = gen_wots_secret_key(&seed, slot, &public_param);
            wots.public_key().hash()
        })
        .collect();
    let mut merkle_tree = vec![leaves];
    // Build levels 1..=LOG_LIFETIME.
    // At level l, we store nodes with index in [(slot_start >> l), (slot_end >> l)].
    // Children outside [slot_start, slot_end]'s subtree are replaced by gen_random_node.
    for level in 1..=LOG_LIFETIME {
        let base = u64::from(slot_start) >> level;
        let top = u64::from(slot_end) >> level;
        let prev_base = u64::from(slot_start) >> (level - 1);
        let prev_top = u64::from(slot_end) >> (level - 1);
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
                        assert!(left_idx < 1u64 << 32);
                        gen_random_node(&seed, level - 1, left_idx as u32)
                    };
                    let right = if right_idx >= prev_base && right_idx <= prev_top {
                        prev[(right_idx - prev_base) as usize]
                    } else {
                        assert!(right_idx < 1u64 << 32);
                        gen_random_node(&seed, level - 1, right_idx as u32)
                    };
                    merkle_hash(&left, &right, level, i as u32, &public_param)
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
        seed,
        public_param,
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
    let pub_key = secret_key.public_key();
    let (randomness, _, _) = find_randomness_for_wots_encoding(message, slot, &pub_key.public_param, rng);
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
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot, &secret_key.public_param);
    let wots_signature = wots_secret_key.sign_with_randomness(message, slot, &secret_key.public_param, randomness);
    let merkle_proof = (0..LOG_LIFETIME)
        .map(|level| {
            let neighbour_index = (slot >> level) ^ 1;
            let base = secret_key.slot_start >> level;
            let top = secret_key.slot_end >> level;
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
) -> Result<(), XmssVerifyError> {
    xmss_verify_with_poseidon_trace(pub_key, message, signature).map(|_| ())
}

pub fn xmss_verify_with_poseidon_trace(
    pub_key: &XmssPublicKey,
    message: &[F; MESSAGE_LEN_FE],
    signature: &XmssSignature,
) -> Result<(Poseidon16History, Poseidon24History), XmssVerifyError> {
    let mut poseidon_16_trace = Vec::new();
    let mut poseidon_24_trace = Vec::new();
    let wots_public_key = signature
        .wots_signature
        .recover_public_key_with_poseidon_trace(
            message,
            signature.slot,
            &pub_key.public_param,
            &signature.wots_signature,
            &mut poseidon_16_trace,
            &mut poseidon_24_trace,
        )
        .ok_or(XmssVerifyError::InvalidWots)?;
    let mut current_hash = wots_public_key.hash_with_poseidon_trace(&mut poseidon_24_trace);
    if signature.merkle_proof.len() != LOG_LIFETIME {
        return Err(XmssVerifyError::InvalidMerklePath);
    }
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = ((signature.slot >> level) & 1) == 0;
        let parent_index = if level + 1 < 32 {
            signature.slot >> (level + 1)
        } else {
            0
        };
        if is_left {
            current_hash = merkle_hash_with_trace(
                &current_hash,
                neighbour,
                level + 1,
                parent_index,
                &pub_key.public_param,
                &mut poseidon_24_trace,
            );
        } else {
            current_hash = merkle_hash_with_trace(
                neighbour,
                &current_hash,
                level + 1,
                parent_index,
                &pub_key.public_param,
                &mut poseidon_24_trace,
            );
        }
    }
    if current_hash == pub_key.merkle_root {
        Ok((poseidon_16_trace, poseidon_24_trace))
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
