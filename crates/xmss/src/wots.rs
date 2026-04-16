use backend::*;
use rand::{CryptoRng, RngExt};
use serde::{Deserialize, Serialize};
use utils::{poseidon8_compress_pair, poseidon_compress_slice};

use crate::*;

#[derive(Debug)]
pub struct WotsSecretKey {
    pub pre_images: [Digest; V],
    public_key: WotsPublicKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WotsSignature {
    #[serde(
        with = "backend::array_serialization",
        bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>")
    )]
    pub chain_tips: [Digest; V],
    pub randomness: [F; RANDOMNESS_LEN_FE],
}

impl WotsSecretKey {
    pub fn random(rng: &mut impl CryptoRng) -> Self {
        Self::new(rng.random())
    }

    pub fn new(pre_images: [Digest; V]) -> Self {
        Self {
            pre_images,
            public_key: WotsPublicKey(std::array::from_fn(|i| iterate_hash(&pre_images[i], CHAIN_LENGTH - 1))),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign_with_randomness(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
        randomness: [F; RANDOMNESS_LEN_FE],
    ) -> WotsSignature {
        let encoding = wots_encode(message, slot, truncated_merkle_root, &randomness).unwrap();
        self.sign_with_encoding(randomness, &encoding)
    }

    fn sign_with_encoding(&self, randomness: [F; RANDOMNESS_LEN_FE], encoding: &[u8; V]) -> WotsSignature {
        WotsSignature {
            chain_tips: std::array::from_fn(|i| iterate_hash(&self.pre_images[i], encoding[i] as usize)),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
        signature: &Self,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message, slot, truncated_merkle_root, &signature.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(&self.chain_tips[i], CHAIN_LENGTH - 1 - encoding[i] as usize)
        })))
    }
}

impl WotsPublicKey {
    pub fn hash(&self) -> Digest {
        let init = poseidon8_compress_pair(&self.0[0], &self.0[1]);
        self.0[2..]
            .iter()
            .fold(init, |digest, chunk| poseidon8_compress_pair(&digest, chunk))
    }
}

pub fn iterate_hash(a: &Digest, n: usize) -> Digest {
    (0..n).fold(*a, |acc, _| poseidon8_compress_pair(&acc, &Default::default()))
}

pub fn find_randomness_for_wots_encoding(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
    rng: &mut impl CryptoRng,
) -> ([F; RANDOMNESS_LEN_FE], [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, slot, truncated_merkle_root, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
    randomness: &[F; RANDOMNESS_LEN_FE],
) -> Option<[u8; V]> {
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);

    const INPUT_LEN: usize = MESSAGE_LEN_FE + RANDOMNESS_LEN_FE + 2 + TRUNCATED_MERKLE_ROOT_LEN_FE;
    let mut input = [F::default(); INPUT_LEN];
    input[..MESSAGE_LEN_FE].copy_from_slice(message);
    input[MESSAGE_LEN_FE..MESSAGE_LEN_FE + RANDOMNESS_LEN_FE].copy_from_slice(randomness);
    input[MESSAGE_LEN_FE + RANDOMNESS_LEN_FE] = slot_lo;
    input[MESSAGE_LEN_FE + RANDOMNESS_LEN_FE + 1] = slot_hi;
    input[MESSAGE_LEN_FE + RANDOMNESS_LEN_FE + 2..].copy_from_slice(truncated_merkle_root);

    let encoding_fe = poseidon_compress_slice(&input, false);

    if encoding_fe.iter().any(|&fe| fe == -F::ONE) {
        return None;
    }

    const CHUNKS_PER_FE: usize = (V + V_GRINDING) / DIGEST_SIZE;
    const MASK: u64 = (1u64 << W) - 1;
    debug_assert_eq!(CHUNKS_PER_FE * DIGEST_SIZE, V + V_GRINDING);

    let mut all_indices = [0u8; V + V_GRINDING];
    for (i, fe) in encoding_fe.iter().enumerate() {
        let value = fe.as_canonical_u64();
        for j in 0..CHUNKS_PER_FE {
            all_indices[i * CHUNKS_PER_FE + j] = ((value >> (j * W)) & MASK) as u8;
        }
    }
    is_valid_encoding(&all_indices).then(|| all_indices[..V].try_into().unwrap())
}

fn is_valid_encoding(encoding: &[u8]) -> bool {
    if encoding.len() != V + V_GRINDING {
        return false;
    }
    // All indices must be < CHAIN_LENGTH
    if !encoding.iter().all(|&x| (x as usize) < CHAIN_LENGTH) {
        return false;
    }
    // First V indices must sum to TARGET_SUM
    if encoding[..V].iter().map(|&x| x as usize).sum::<usize>() != TARGET_SUM {
        return false;
    }
    // Last V_GRINDING indices must all be CHAIN_LENGTH-1 (grinding constraint)
    if !encoding[V..].iter().all(|&x| x as usize == CHAIN_LENGTH - 1) {
        return false;
    }
    true
}

pub fn slot_to_field_elements(slot: u32) -> [F; 2] {
    [
        F::from_usize((slot & 0xFFFF) as usize),
        F::from_usize(((slot >> 16) & 0xFFFF) as usize),
    ]
}
