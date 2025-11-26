use multilinear_toolkit::prelude::*;
use rand::{SeedableRng, rngs::StdRng};
use sha3::{Digest as Sha3Digest, Keccak256};

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey {
    pub(crate) first_slot: u64,
    pub(crate) seed: [u8; 32],
    pub(crate) merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub slot: u64, // unused for now (Toy XMSS)
    pub merkle_proof: Vec<Digest>,
}

#[derive(Debug)]
pub struct XmssPublicKey {
    pub merkle_root: Digest,
    pub first_slot: u64,
    pub log_lifetime: usize,
}

fn gen_wots_secret_key(seed: &[u8; 32], slot: u64) -> WotsSecretKey {
    let mut hasher = Keccak256::new();
    hasher.update(seed);
    hasher.update(slot.to_le_bytes());
    let mut rng = StdRng::from_seed(hasher.finalize().into());
    WotsSecretKey::random(&mut rng)
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssKeyGenError {
    LogLifetimeTooSmall,
    LogLifetimeTooLarge,
    FirstSlotTooLarge,
}

pub fn xmss_key_gen(
    seed: [u8; 32],
    first_slot: u64,
    log_lifetime: usize,
) -> Result<(XmssSecretKey, XmssPublicKey), XmssKeyGenError> {
    if first_slot >= (1 << XMSS_MAX_LOG_LIFETIME) {
        return Err(XmssKeyGenError::FirstSlotTooLarge);
    }
    if log_lifetime == 0 {
        return Err(XmssKeyGenError::LogLifetimeTooSmall);
    }
    if log_lifetime > XMSS_MAX_LOG_LIFETIME {
        return Err(XmssKeyGenError::LogLifetimeTooLarge);
    }
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
    let pub_key = XmssPublicKey {
        first_slot,
        merkle_root: *merkle_tree.last().unwrap().first().unwrap(),
        log_lifetime,
    };
    let secret_key = XmssSecretKey {
        first_slot,
        seed,
        merkle_tree,
    };
    Ok((secret_key, pub_key))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssSignatureError {
    SlotTooEarly,
    SlotTooLate,
}

pub fn xmss_sign(
    randomness_seed: [u8; 32],
    secret_key: &XmssSecretKey,
    message_hash: &[F; 8],
    slot: u64,
) -> Result<XmssSignature, XmssSignatureError> {
    if slot < secret_key.first_slot {
        return Err(XmssSignatureError::SlotTooEarly);
    }
    let wots_index = slot - secret_key.first_slot;
    if wots_index >= secret_key.lifetime() {
        return Err(XmssSignatureError::SlotTooLate);
    }
    let wots_secret_key = gen_wots_secret_key(&secret_key.seed, slot);
    let mut rng = StdRng::from_seed(randomness_seed);
    let wots_signature = wots_secret_key.sign(message_hash, &mut rng);
    let merkle_proof = (0..secret_key.log_lifetime())
        .scan(wots_index, |current_idx, level| {
            let neighbour_index = *current_idx ^ 1;
            // TODO edge case if usize = u32 and MAX_LOG_LIFETIME > 32 ? (unlikely)
            let neighbour = secret_key.merkle_tree[level][neighbour_index as usize];
            // Move up to the next level.
            *current_idx /= 2;
            Some(neighbour)
        })
        .collect();
    Ok(XmssSignature {
        wots_signature,
        slot,
        merkle_proof,
    })
}

impl XmssSecretKey {
    pub fn log_lifetime(&self) -> usize {
        self.merkle_tree.len() - 1
    }

    pub fn lifetime(&self) -> u64 {
        1 << self.log_lifetime()
    }

    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            first_slot: self.first_slot,
            merkle_root: self.merkle_tree.last().unwrap()[0],
            log_lifetime: self.log_lifetime(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum XmssVerifyError {
    SlotTooEarly,
    SlotTooLate,
    InvalidWots,
    InvalidMerklePath,
}

pub fn xmss_verify(
    pub_key: &XmssPublicKey,
    message_hash: &Digest,
    signature: &XmssSignature,
) -> Result<(), XmssVerifyError> {
    xmss_verify_with_poseidon_trace(pub_key, message_hash, signature).map(|_| ())
}

pub fn xmss_verify_with_poseidon_trace(
    pub_key: &XmssPublicKey,
    message_hash: &Digest,
    signature: &XmssSignature,
) -> Result<(Poseidon16History, Poseidon24History), XmssVerifyError> {
    if signature.slot < pub_key.first_slot {
        return Err(XmssVerifyError::SlotTooEarly);
    }
    let wots_index = signature.slot - pub_key.first_slot;
    if wots_index >= (1 << pub_key.log_lifetime) {
        return Err(XmssVerifyError::SlotTooLate);
    }
    let mut poseidon_16_trace = Vec::new();
    let mut poseidon_24_trace = Vec::new();
    let wots_public_key = signature
        .wots_signature
        .recover_public_key_with_poseidon_trace(message_hash, &signature.wots_signature, &mut poseidon_16_trace)
        .ok_or(XmssVerifyError::InvalidWots)?;
    // merkle root verification
    let mut current_hash = wots_public_key.hash_with_poseidon_trace(&mut poseidon_24_trace);
    if signature.merkle_proof.len() != pub_key.log_lifetime {
        return Err(XmssVerifyError::InvalidMerklePath);
    }
    for (level, neighbour) in signature.merkle_proof.iter().enumerate() {
        let is_left = ((wots_index >> level) & 1) == 0;
        if is_left {
            current_hash = poseidon16_compress_with_trace(&current_hash, neighbour, &mut poseidon_16_trace)
        } else {
            current_hash = poseidon16_compress_with_trace(neighbour, &current_hash, &mut poseidon_16_trace);
        }
    }
    if current_hash == pub_key.merkle_root {
        Ok((poseidon_16_trace, poseidon_24_trace))
    } else {
        Err(XmssVerifyError::InvalidMerklePath)
    }
}
