use multilinear_toolkit::prelude::*;
use p3_symmetric::Permutation;
use rand::{CryptoRng, Rng};
use utils::{ToUsize, get_poseidon16, poseidon16_compress_pair, to_little_endian_bits};

use crate::*;

#[derive(Debug)]
pub struct WotsSecretKey {
    pub pre_images: [Digest; V],
    public_key: WotsPublicKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; V]);

#[derive(Debug, Clone)]
pub struct WotsSignature {
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

    pub fn sign(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
        rng: &mut impl CryptoRng,
    ) -> WotsSignature {
        let (randomness, encoding, _) = find_randomness_for_wots_encoding(message, slot, truncated_merkle_root, rng);
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
        self.recover_public_key_with_poseidon_trace(message, slot, truncated_merkle_root, signature, &mut Vec::new())
    }

    pub fn recover_public_key_with_poseidon_trace(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
        signature: &Self,
        poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode_with_poseidon_trace(
            message,
            slot,
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
        let init = poseidon16_compress_with_trace(&self.0[0], &self.0[1], poseidon_16_trace);
        self.0[2..].iter().fold(init, |digest, chunk| {
            poseidon16_compress_with_trace(&digest, chunk, poseidon_16_trace)
        })
    }
}

pub fn iterate_hash(a: &Digest, n: usize) -> Digest {
    (0..n).fold(*a, |acc, _| poseidon16_compress_pair(acc, Default::default()))
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
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
    rng: &mut impl CryptoRng,
) -> ([F; RANDOMNESS_LEN_FE], [u8; V], usize) {
    let lanes = FPacking::<F>::WIDTH;
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);
    let poseidon = get_poseidon16();

    let mut num_batches = 0;
    loop {
        num_batches += 1;

        let randomness_batch: Vec<[F; RANDOMNESS_LEN_FE]> = (0..lanes).map(|_| rng.random()).collect();

        let mut input_a = [FPacking::<F>::from(F::ZERO); 16];
        for i in 0..8 {
            input_a[i] = FPacking::<F>::from(message[i]);
        }
        input_a[8] = FPacking::<F>::from(message[8]);
        for j in 0..RANDOMNESS_LEN_FE {
            input_a[9 + j] = FPacking::<F>::from_fn(|lane| randomness_batch[lane][j]);
        }

        let output_a = poseidon.permute(input_a);

        let mut input_b = [FPacking::<F>::from(F::ZERO); 16];
        input_b[..8].copy_from_slice(&output_a[..8]);
        input_b[8] = FPacking::<F>::from(slot_lo);
        input_b[9] = FPacking::<F>::from(slot_hi);
        for i in 0..TRUNCATED_MERKLE_ROOT_LEN_FE {
            input_b[10 + i] = FPacking::<F>::from(truncated_merkle_root[i]);
        }

        let output_b = poseidon.permute(input_b);

        for (lane, randomness) in randomness_batch.iter().enumerate() {
            let compressed: [F; 8] = std::array::from_fn(|i| output_b[i].as_slice()[lane]);

            if compressed.iter().any(|&kb| kb == -F::ONE) {
                continue;
            }

            let all_indices: Vec<u8> = compressed
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

            if is_valid_encoding(&all_indices) {
                return (
                    *randomness,
                    all_indices[..V].try_into().unwrap(),
                    (num_batches - 1) * lanes + lane + 1,
                );
            }
        }
    }
}

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
    randomness: &[F; RANDOMNESS_LEN_FE],
) -> Option<[u8; V]> {
    wots_encode_with_poseidon_trace(message, slot, truncated_merkle_root, randomness, &mut Vec::new())
}

pub fn wots_encode_with_poseidon_trace(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    truncated_merkle_root: &[F; TRUNCATED_MERKLE_ROOT_LEN_FE],
    randomness: &[F; RANDOMNESS_LEN_FE],
    poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
) -> Option<[u8; V]> {
    // Encode slot as 2 field elements (16 bits each)
    let [slot_lo, slot_hi] = slot_to_field_elements(slot);

    // A = poseidon(message (9 fe), randomness (7 fe))
    let mut a_input_right = [F::default(); 8];
    a_input_right[0] = message[8];
    a_input_right[1..1 + RANDOMNESS_LEN_FE].copy_from_slice(randomness);
    let a = poseidon16_compress_with_trace(message[..8].try_into().unwrap(), &a_input_right, poseidon_16_trace);

    // B = poseidon(A (8 fe), slot (2 fe), truncated_merkle_root (6 fe))
    let mut b_input_right = [F::default(); 8];
    b_input_right[0] = slot_lo;
    b_input_right[1] = slot_hi;
    b_input_right[2..8].copy_from_slice(truncated_merkle_root);
    let compressed = poseidon16_compress_with_trace(&a, &b_input_right, poseidon_16_trace);

    if compressed.iter().any(|&kb| kb == -F::ONE) {
        // ensures uniformity of encoding
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

pub fn slot_to_field_elements(slot: u32) -> [F; 2] {
    [
        F::from_usize((slot & 0xFFFF) as usize),
        F::from_usize(((slot >> 16) & 0xFFFF) as usize),
    ]
}
