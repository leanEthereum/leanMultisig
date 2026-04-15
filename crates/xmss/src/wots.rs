use backend::*;
use rand::{CryptoRng, RngExt};
use serde::{Deserialize, Serialize};
use utils::{ToUsize, poseidon8_compress_pair};

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
        // TODO(goldilocks-migration): re-derive WOTS hashing over width-8 Poseidon /
        // digest-4. The KoalaBear version chained 8-element digests through a width-16
        // permutation; the parameter layout doesn't port one-to-one. Stubbed for now
        // because XMSS isn't exercised by `test_zk_vm_all_precompiles`.
        unimplemented!("WOTS hash not yet reworked for Goldilocks digest-4")
    }
}

pub fn iterate_hash(_a: &Digest, _n: usize) -> Digest {
    // TODO(goldilocks-migration): see `WotsPublicKey::hash`.
    unimplemented!("WOTS iterate_hash not yet reworked for Goldilocks digest-4")
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
    _message: &[F; MESSAGE_LEN_FE],
    _slot: u32,
    _truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
    _randomness: &[F; RANDOMNESS_LEN_FE],
) -> Option<[u8; V]> {
    // TODO(goldilocks-migration): WOTS encoding depends on Poseidon width 16 / digest 8
    // layout, and on a 24-bit little-endian decomposition of a 31-bit KoalaBear value.
    // For Goldilocks we need a fresh parameter choice (64-bit lanes, width-8 permutation,
    // digest-4). Stubbed for now because XMSS isn't exercised by
    // `test_zk_vm_all_precompiles`.
    unimplemented!("WOTS encoding not yet reworked for Goldilocks")
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
