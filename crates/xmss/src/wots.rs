use p3_util::log2_strict_usize;
use rand::Rng;
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
    pub fn random(rng: &mut impl Rng) -> Self {
        let mut pre_images = [Default::default(); V];
        for i in 0..V {
            let mut pre_image = Digest::default();
            for j in 0..8 {
                pre_image[j] = rng.random();
            }
            pre_images[i] = pre_image;
        }
        Self::new(pre_images)
    }

    pub fn new(pre_images: [Digest; V]) -> Self {
        let mut public_key = [Default::default(); V];
        for i in 0..V {
            public_key[i] = iterate_hash(&pre_images[i], W - 1, i % 2 == 1);
        }
        Self {
            pre_images,
            public_key: WotsPublicKey(public_key),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign(&self, message_hash: &Digest, rng: &mut impl Rng) -> WotsSignature {
        let (randomness, encoding) = find_randomness_for_wots_encoding(message_hash, rng);
        let mut chain_tips = [Default::default(); V];
        for i in 0..V {
            chain_tips[i] = iterate_hash(&self.pre_images[i], encoding[i] as usize, i % 2 == 1);
        }
        WotsSignature {
            chain_tips,
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
        let mut public_key = [Default::default(); V];
        for i in 0..V {
            public_key[i] = iterate_hash(
                &signature.chain_tips[i],
                W - 1 - encoding[i] as usize,
                i % 2 == 1,
            );
        }
        Some(WotsPublicKey(public_key))
    }
}

impl WotsPublicKey {
    pub fn hash(&self) -> Digest {
        assert!(V % 2 == 0);
        let mut digest = Default::default();
        for (a, b) in self.0.chunks(2).map(|chunk| (chunk[0], chunk[1])) {
            digest = poseidon24_compress(&a, &b, &digest);
        }
        digest
    }
}

fn iterate_hash(a: &Digest, n: usize, keep_left: bool) -> Digest {
    let mut res = *a;
    for _ in 0..n {
        res = if keep_left {
            poseidon16_compress(&res, &Default::default())
        } else {
            poseidon16_compress_right(&Default::default(), &res)
        };
    }
    res
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
    let encoding = compressed
        .iter()
        .flat_map(|kb| to_little_endian_bits(kb.to_usize(), 24))
        .collect::<Vec<_>>()
        .chunks_exact(log2_strict_usize(W))
        .take(V)
        .map(|chunk| {
            let mut num = 0;
            for (index, bit) in chunk.iter().enumerate() {
                num += (*bit as u8) << index;
            }
            num
        })
        .collect::<Vec<_>>();
    is_valid_encoding(&encoding).then(|| encoding.try_into().unwrap())
}

fn is_valid_encoding(encoding: &[u8]) -> bool {
    encoding.len() == V
        && encoding.iter().all(|&x| (x as usize) < W)
        && encoding.iter().map(|&x| x as usize).sum::<usize>() == TARGET_SUM
}
