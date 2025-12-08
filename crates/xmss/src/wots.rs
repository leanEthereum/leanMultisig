use multilinear_toolkit::prelude::*;
use p3_util::log2_strict_usize;
use rand::{Rng, RngCore};
use utils::{ToUsize, to_little_endian_bits};

use crate::*;

#[derive(Debug)]
pub struct WotsSecretKey {
    pub pre_images: [Digest; V],
    public_key: WotsPublicKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug)]
pub struct WotsSignature {
    pub chain_tips: [Digest; V],
    pub randomness: Digest,
}

impl WotsSecretKey {
    pub fn random(rng: &mut impl RngCore) -> Self {
        Self::new(rng.random())
    }

    pub fn new(pre_images: [Digest; V]) -> Self {
        Self {
            pre_images,
            public_key: WotsPublicKey(std::array::from_fn(|i| iterate_hash(&pre_images[i], W - 1))),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign(&self, message_hash: &Digest, rng: &mut impl Rng) -> WotsSignature {
        let (randomness, encoding) = find_randomness_for_wots_encoding(message_hash, rng);
        WotsSignature {
            chain_tips: std::array::from_fn(|i| iterate_hash(&self.pre_images[i], encoding[i] as usize)),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(&self, message_hash: &Digest, signature: &Self) -> Option<WotsPublicKey> {
        self.recover_public_key_with_poseidon_trace(message_hash, signature, &mut Vec::new())
    }

    pub fn recover_public_key_with_poseidon_trace(
        &self,
        message_hash: &Digest,
        signature: &Self,
        poseidon_16_trace: &mut Vec<([F; 16], [F; 16])>,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode_with_poseidon_trace(message_hash, &signature.randomness, poseidon_16_trace)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash_with_poseidon_trace(&self.chain_tips[i], W - 1 - encoding[i] as usize, poseidon_16_trace)
        })))
    }
}

impl WotsPublicKey {
    pub fn hash(&self) -> Digest {
        self.hash_with_poseidon_trace(&mut Vec::new())
    }

    pub fn hash_with_poseidon_trace(&self, poseidon_16_trace: &mut Poseidon16History) -> Digest {
        self.0.iter().fold(Digest::default(), |digest, chunk| {
            poseidon16_compress_with_trace(&digest, chunk, poseidon_16_trace)
        })
    }
}

pub fn iterate_hash(a: &Digest, n: usize) -> Digest {
    (0..n).fold(*a, |acc, _| poseidon16_compress(&acc, &Default::default()))
}

pub fn iterate_hash_with_poseidon_trace(
    a: &Digest,
    n: usize,
    poseidon_16_trace: &mut Vec<([F; 16], [F; 16])>,
) -> Digest {
    (0..n).fold(*a, |acc, _| {
        poseidon16_compress_with_trace(&acc, &Default::default(), poseidon_16_trace)
    })
}

pub fn find_randomness_for_wots_encoding(message: &Digest, rng: &mut impl Rng) -> (Digest, [u8; V]) {
    loop {
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, &randomness) {
            return (randomness, encoding);
        }
    }
}

pub fn wots_encode(message: &Digest, randomness: &Digest) -> Option<[u8; V]> {
    wots_encode_with_poseidon_trace(message, randomness, &mut Vec::new())
}

pub fn wots_encode_with_poseidon_trace(
    message: &Digest,
    randomness: &Digest,
    poseidon_16_trace: &mut Vec<([F; 16], [F; 16])>,
) -> Option<[u8; V]> {
    let compressed = poseidon16_compress_with_trace(message, randomness, poseidon_16_trace);
    if compressed.iter().any(|&kb| kb == -F::ONE) {
        return None;
    }
    let encoding: Vec<_> = compressed
        .iter()
        .flat_map(|kb| to_little_endian_bits(kb.to_usize(), 24))
        .collect::<Vec<_>>()
        .chunks_exact(log2_strict_usize(W))
        .take(V)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |acc, (i, &bit)| acc | (u8::from(bit) << i))
        })
        .collect();
    is_valid_encoding(&encoding).then(|| encoding.try_into().unwrap())
}

fn is_valid_encoding(encoding: &[u8]) -> bool {
    encoding.len() == V
        && encoding.iter().all(|&x| (x as usize) < W)
        && encoding.iter().map(|&x| x as usize).sum::<usize>() == TARGET_SUM
}
