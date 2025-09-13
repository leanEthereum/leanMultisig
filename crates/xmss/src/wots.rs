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
            public_key: WotsPublicKey(std::array::from_fn(|i| {
                iterate_hash(&pre_images[i], W - 1, i % 2 == 1)
            })),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign(&self, message_hash: &Digest, rng: &mut impl Rng) -> WotsSignature {
        let (randomness, encoding) = find_randomness_for_wots_encoding(message_hash, rng);
        WotsSignature {
            chain_tips: std::array::from_fn(|i| {
                iterate_hash(&self.pre_images[i], encoding[i] as usize, i % 2 == 1)
            }),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message_hash: &Digest,
        signature: &Self,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message_hash, &signature.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(
                &self.chain_tips[i],
                W - 1 - encoding[i] as usize,
                i % 2 == 1,
            )
        })))
    }
}

impl WotsPublicKey {
    pub fn hash(&self) -> Digest {
        assert!(V.is_multiple_of(2), "V must be even for hashing pairs.");
        self.0
            .chunks_exact(2)
            .fold(Digest::default(), |digest, chunk| {
                poseidon24_compress(&chunk[0], &chunk[1], &digest)
            })
    }
}

fn iterate_hash(a: &Digest, n: usize, keep_left: bool) -> Digest {
    (0..n).fold(*a, |acc, _| {
        if keep_left {
            poseidon16_compress(&acc, &Default::default())
        } else {
            poseidon16_compress_right(&Default::default(), &acc)
        }
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &Digest,
    rng: &mut impl Rng,
) -> (Digest, [u8; V]) {
    loop {
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, &randomness) {
            return (randomness, encoding);
        }
    }
}

pub fn wots_encode(message: &Digest, randomness: &Digest) -> Option<[u8; V]> {
    let compressed = poseidon16_compress(message, randomness);
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
