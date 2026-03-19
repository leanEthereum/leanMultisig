use backend::*;
use rand::{CryptoRng, Rng};
use serde::{Deserialize, Serialize};
use utils::{ToUsize, poseidon16_compress, to_little_endian_bits};

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
    pub fn random(rng: &mut impl CryptoRng, public_param: &PublicParam, slot: u32) -> Self {
        Self::new(rng.random(), public_param, slot)
    }

    pub fn new(pre_images: [Digest; V], public_param: &PublicParam, slot: u32) -> Self {
        Self {
            pre_images,
            public_key: WotsPublicKey(std::array::from_fn(|i| {
                iterate_hash(&pre_images[i], CHAIN_LENGTH - 1, public_param, slot, i, 0)
            })),
        }
    }

    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    pub fn sign_with_randomness(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        public_param: &PublicParam,
        randomness: [F; RANDOMNESS_LEN_FE],
    ) -> WotsSignature {
        let encoding = wots_encode(message, slot, public_param, &randomness).unwrap();
        self.sign_with_encoding(randomness, &encoding, public_param, slot)
    }

    fn sign_with_encoding(
        &self,
        randomness: [F; RANDOMNESS_LEN_FE],
        encoding: &[u8; V],
        public_param: &PublicParam,
        slot: u32,
    ) -> WotsSignature {
        WotsSignature {
            chain_tips: std::array::from_fn(|i| {
                iterate_hash(&self.pre_images[i], encoding[i] as usize, public_param, slot, i, 0)
            }),
            randomness,
        }
    }
}

impl WotsSignature {
    pub fn recover_public_key(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        public_param: &PublicParam,
        signature: &Self,
    ) -> Option<WotsPublicKey> {
        self.recover_public_key_with_poseidon_trace(
            message,
            slot,
            public_param,
            signature,
            &mut Vec::new(),
            &mut Vec::new(),
        )
    }

    pub fn recover_public_key_with_poseidon_trace(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        public_param: &PublicParam,
        signature: &Self,
        poseidon_16_trace: &mut Poseidon16History,
        poseidon_24_trace: &mut Poseidon24History,
    ) -> Option<WotsPublicKey> {
        let encoding =
            wots_encode_with_poseidon_trace(message, slot, public_param, &signature.randomness, poseidon_24_trace)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash_with_poseidon_trace(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                public_param,
                slot,
                i,
                encoding[i] as usize,
                poseidon_16_trace,
            )
        })))
    }
}

impl WotsPublicKey {
    pub fn hash(&self) -> Digest {
        self.hash_with_poseidon_trace(&mut Vec::new())
    }

    /// Hash the WOTS public key via Poseidon24 sponge absorbing flat chain data at rate 15.
    /// V*8 FE absorbed in ceil(V*8/15) steps.
    pub fn hash_with_poseidon_trace(&self, poseidon_24_trace: &mut Poseidon24History) -> Digest {
        let flat: Vec<F> = self.0.iter().flat_map(|d| d.iter().copied()).collect();
        let mut capacity = [F::ZERO; POSEIDON24_CAPACITY];
        for chunk in flat.chunks(POSEIDON24_RATE) {
            let mut input = [F::ZERO; 24];
            input[..POSEIDON24_CAPACITY].copy_from_slice(&capacity);
            input[POSEIDON24_CAPACITY..POSEIDON24_CAPACITY + chunk.len()].copy_from_slice(chunk);
            // remaining positions are zero (padding for last chunk if V*8 % 15 != 0)
            capacity = poseidon24_compress_with_trace(input, poseidon_24_trace);
        }
        capacity[..DIGEST_SIZE].try_into().unwrap()
    }
}

/// Chain hash using Poseidon16: digest(8) || tweak(2) || public_param(5) || zero(1) = 16
pub fn iterate_hash(
    a: &Digest,
    n: usize,
    public_param: &PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let mut input = [F::ZERO; 16];
        input[0..DIGEST_SIZE].copy_from_slice(&acc);
        input[DIGEST_SIZE..DIGEST_SIZE + TWEAK_LEN].copy_from_slice(&tweak);
        input[DIGEST_SIZE + TWEAK_LEN..DIGEST_SIZE + TWEAK_LEN + PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
        // input[15] = F::ZERO (padding); total = 8+2+5+1 = 16
        poseidon16_compress(input)
    })
}

pub fn iterate_hash_with_poseidon_trace(
    a: &Digest,
    n: usize,
    public_param: &PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
    poseidon_16_trace: &mut Poseidon16History,
) -> Digest {
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let mut input = [F::ZERO; 16];
        input[0..DIGEST_SIZE].copy_from_slice(&acc);
        input[DIGEST_SIZE..DIGEST_SIZE + TWEAK_LEN].copy_from_slice(&tweak);
        input[DIGEST_SIZE + TWEAK_LEN..DIGEST_SIZE + TWEAK_LEN + PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
        poseidon16_compress_with_trace(input, poseidon_16_trace)
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    public_param: &PublicParam,
    rng: &mut impl CryptoRng,
) -> ([F; RANDOMNESS_LEN_FE], [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, slot, public_param, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    public_param: &PublicParam,
    randomness: &[F; RANDOMNESS_LEN_FE],
) -> Option<[u8; V]> {
    wots_encode_with_poseidon_trace(message, slot, public_param, randomness, &mut Vec::new())
}

/// Encode (message, slot, public_param, randomness) into V chain indices via Poseidon24.
/// Input layout: message(9) || tweak(2) || randomness(7) || public_param(5) || padding(1) = 24
/// Output: 9 field elements. Each provides 24/W = 8 values at W bits. Take first V.
pub fn wots_encode_with_poseidon_trace(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    public_param: &PublicParam,
    randomness: &[F; RANDOMNESS_LEN_FE],
    poseidon_24_trace: &mut Poseidon24History,
) -> Option<[u8; V]> {
    let tweak = make_tweak(TWEAK_TYPE_ENCODING, 0, slot);

    let mut input = [F::ZERO; 24];
    input[0..MESSAGE_LEN_FE].copy_from_slice(message); // 9
    input[MESSAGE_LEN_FE..MESSAGE_LEN_FE + TWEAK_LEN].copy_from_slice(&tweak); // 2
    input[MESSAGE_LEN_FE + TWEAK_LEN..MESSAGE_LEN_FE + TWEAK_LEN + RANDOMNESS_LEN_FE].copy_from_slice(randomness); // 7
    input[MESSAGE_LEN_FE + TWEAK_LEN + RANDOMNESS_LEN_FE
        ..MESSAGE_LEN_FE + TWEAK_LEN + RANDOMNESS_LEN_FE + PUBLIC_PARAM_LEN_FE]
        .copy_from_slice(public_param); // 5
    // input[23] = F::ZERO (padding); total = 9+2+7+5+1 = 24

    let compressed = poseidon24_compress_with_trace(input, poseidon_24_trace);

    if compressed.iter().any(|&kb| kb == -F::ONE) {
        // ensures uniformity of encoding
        return None;
    }

    // Extract V values from 9 output elements.
    // Each element provides 24/W = 8 values at W=3 bits each (24 bits used).
    // 9 elements * 8 values = 72 total, take first V.
    let bits_per_element = (24 / W) * W; // 24

    let all_indices: Vec<_> = compressed
        .iter()
        .flat_map(|kb| to_little_endian_bits(kb.to_usize(), bits_per_element))
        .collect::<Vec<_>>()
        .chunks_exact(W)
        .take(V)
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
    if encoding.len() != V {
        return false;
    }
    // All indices must be < CHAIN_LENGTH
    if !encoding.iter().all(|&x| (x as usize) < CHAIN_LENGTH) {
        return false;
    }
    // Indices must sum to TARGET_SUM
    if encoding.iter().map(|&x| x as usize).sum::<usize>() != TARGET_SUM {
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
