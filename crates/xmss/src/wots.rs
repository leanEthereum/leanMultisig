use multilinear_toolkit::prelude::*;
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
            public_key: WotsPublicKey(std::array::from_fn(|i| iterate_hash(&pre_images[i], CHAIN_LENGTH - 1))),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign(
        &self,
        message_hash: &Digest,
        epoch: u32,
        truncated_merkle_root: &[F; 6],
        rng: &mut impl Rng,
    ) -> WotsSignature {
        let (randomness, encoding, _) =
            find_randomness_for_wots_encoding(message_hash, epoch, truncated_merkle_root, rng);
        WotsSignature {
            chain_tips: std::array::from_fn(|i| iterate_hash(&self.pre_images[i], encoding[i] as usize)),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message_hash: &Digest,
        epoch: u32,
        truncated_merkle_root: &[F; 6],
        signature: &Self,
    ) -> Option<WotsPublicKey> {
        self.recover_public_key_with_poseidon_trace(
            message_hash,
            epoch,
            truncated_merkle_root,
            signature,
            &mut Vec::new(),
        )
    }

    pub fn recover_public_key_with_poseidon_trace(
        &self,
        message_hash: &Digest,
        epoch: u32,
        truncated_merkle_root: &[F; 6],
        signature: &Self,
        poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode_with_poseidon_trace(
            message_hash,
            epoch,
            truncated_merkle_root,
            &signature.randomness,
            poseidon_16_trace,
        )?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash_with_poseidon_trace(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                poseidon_16_trace,
            )
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
    (0..n).fold(*a, |acc, _| {
        poseidon16_compress([acc, Default::default()].concat().try_into().unwrap())
    })
}

pub fn iterate_hash_with_poseidon_trace(
    a: &Digest,
    n: usize,
    poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
) -> Digest {
    (0..n).fold(*a, |acc, _| {
        poseidon16_compress_with_trace(&acc, &Default::default(), poseidon_16_trace)
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &Digest,
    epoch: u32,
    truncated_merkle_root: &[F; 6],
    rng: &mut impl Rng,
) -> (Digest, [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, epoch, truncated_merkle_root, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

pub fn wots_encode(
    message: &Digest,
    epoch: u32,
    truncated_merkle_root: &[F; 6],
    randomness: &Digest,
) -> Option<[u8; V]> {
    wots_encode_with_poseidon_trace(message, epoch, truncated_merkle_root, randomness, &mut Vec::new())
}

pub fn wots_encode_with_poseidon_trace(
    message: &Digest,
    epoch: u32,
    truncated_merkle_root: &[F; 6],
    randomness: &Digest,
    poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
) -> Option<[u8; V]> {
    // Encode epoch as 2 field elements (16 bits each)
    let epoch_lo = F::from_usize((epoch & 0xFFFF) as usize);
    let epoch_hi = F::from_usize(((epoch >> 16) & 0xFFFF) as usize);

    // A = poseidon(message (8 fe), epoch (2 fe), truncated_merkle_root (6 fe))
    let mut epoch_and_root = [F::default(); 8];
    epoch_and_root[0] = epoch_lo;
    epoch_and_root[1] = epoch_hi;
    epoch_and_root[2..8].copy_from_slice(truncated_merkle_root);
    let a = poseidon16_compress_with_trace(message, &epoch_and_root, poseidon_16_trace);

    // B = poseidon(A (8 fe), randomness (8 fe))
    let compressed = poseidon16_compress_with_trace(&a, randomness, poseidon_16_trace);

    if compressed.iter().any(|&kb| kb == -F::ONE) {
        return None;
    }
    let all_indices: Vec<_> = compressed
        .iter()
        .flat_map(|kb| to_little_endian_bits(kb.to_usize(), 24))
        .collect::<Vec<_>>()
        .chunks_exact(W)
        .take(V + V_GRINDING)
        .map(|chunk| {
            chunk
                .iter()
                .enumerate()
                .fold(0u8, |acc, (i, &bit)| acc | (u8::from(bit) << i))
        })
        .collect();
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
