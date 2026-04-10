use backend::*;
use rand::{CryptoRng, RngExt};
use serde::{Deserialize, Serialize};
use utils::{ToUsize, poseidon16_compress_pair, to_little_endian_bits};

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
    pub randomness: Randomness,
}

impl WotsSecretKey {
    pub fn random(rng: &mut impl CryptoRng, public_param: PublicParam, slot: u32) -> Self {
        Self::new(rng.random(), public_param, slot)
    }

    pub fn new(pre_images: [Digest; V], public_param: PublicParam, slot: u32) -> Self {
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
        xmss_pub_key: &XmssPublicKey,
        randomness: Randomness,
    ) -> WotsSignature {
        let encoding = wots_encode(message, slot, xmss_pub_key, &randomness).unwrap();
        self.sign_with_encoding(randomness, &encoding, xmss_pub_key.public_param, slot)
    }

    fn sign_with_encoding(
        &self,
        randomness: Randomness,
        encoding: &[u8; V],
        public_param: PublicParam,
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
        xmss_pub_key: &XmssPublicKey,
        signature: &Self,
    ) -> Option<WotsPublicKey> {
        let encoding = wots_encode(message, slot, xmss_pub_key, &signature.randomness)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                xmss_pub_key.public_param,
                slot,
                i,
                encoding[i] as usize,
            )
        })))
    }
}

impl WotsPublicKey {
    /// Sponge-like hash of V public key digests.
    /// IV = [tweak(2) | 00(2) | pp(4)]; first absorb 8 zeros, then ingest 8 FE per step
    /// (2 digests at a time). The leading zero-absorb gives the SNARK-side a uniform
    /// per-pair loop starting at i=0 and lets each pair live in a 10-FE slot
    /// `[leading_0 | tip_a | tip_b | trailing_0]`, with the leading/trailing zero cells
    /// serving as copy_5 slack in `chain_hash_pair`.
    /// The IV layout matches the LEFT-input convention for `poseidon16_compress_hardcoded_left_4`
    /// — `[tweak(2) | 00]` is read straight from the wots_pk tweak slot, and `[pp(4)]` lives at
    /// the runtime public_param pointer. Final output truncated to DIGEST_SIZE (4 FE).
    pub fn hash(&self, public_param: PublicParam, slot: u32) -> Digest {
        assert!(V % 2 == 0);
        // IV: [tweak(2) | 00 | pp(4)]
        let tweak = make_tweak(TWEAK_TYPE_WOTS_PK, 0, slot);
        let mut state = [F::default(); 8];
        state[..TWEAK_LEN].copy_from_slice(&tweak);
        // state[2..4] = 00 (default)
        state[4..4 + PUBLIC_PARAM_LEN_FE].copy_from_slice(&public_param);

        // Initial absorb of 8 zeros (matches the SNARK's `poseidon16_compress_hardcoded_left_4`
        // call against `ZERO_VEC_PTR` in `wots_pk_hash`).
        let zeros = [F::ZERO; 8];
        state = poseidon16_compress_pair(&state, &zeros);

        for i in (0..V).step_by(2) {
            let mut chunk = [F::default(); 8];
            chunk[..XMSS_DIGEST_LEN].copy_from_slice(&self.0[i]);
            chunk[XMSS_DIGEST_LEN..].copy_from_slice(&self.0[i + 1]);
            state = poseidon16_compress_pair(&state, &chunk);
        }
        state[..XMSS_DIGEST_LEN].try_into().unwrap()
    }
}

pub fn iterate_hash(
    a: &Digest,
    n: usize,
    public_param: PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    // Chain hash layout: left = [tweak | zeros | data], right = [pp | zeros] (constant).
    let right = build_right_chain_pp(&public_param);
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left_chain(tweak, &acc);
        poseidon16_compress_pair(&left, &right)[..XMSS_DIGEST_LEN]
            .try_into()
            .unwrap()
    })
}

pub fn iterate_hash_with_poseidon_trace(
    a: &Digest,
    n: usize,
    poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
    public_param: PublicParam,
    slot: u32,
    chain_index: usize,
    start_step: usize,
) -> Digest {
    // Chain hash layout: left = [tweak | zeros | data], right = [pp | zeros] (constant).
    let right = build_right_chain_pp(&public_param);
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left_chain(tweak, &acc);
        poseidon16_compress_with_trace(left, right, poseidon_16_trace)[..XMSS_DIGEST_LEN]
            .try_into()
            .unwrap()
    })
}

pub fn find_randomness_for_wots_encoding(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    rng: &mut impl CryptoRng,
) -> (Randomness, [u8; V], usize) {
    let mut num_iters = 0;
    loop {
        num_iters += 1;
        let randomness = rng.random();
        if let Some(encoding) = wots_encode(message, slot, xmss_pub_key, &randomness) {
            return (randomness, encoding, num_iters);
        }
    }
}

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    randomness: &Randomness,
) -> Option<[u8; V]> {
    wots_encode_with_poseidon_trace(message, slot, xmss_pub_key, randomness, &mut Vec::new())
}

pub fn wots_encode_with_poseidon_trace(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    randomness: &Randomness,
    poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
) -> Option<[u8; V]> {
    let mut first_input_right = [F::default(); 8];
    first_input_right[0] = message[8];
    first_input_right[1..1 + RANDOMNESS_LEN_FE].copy_from_slice(randomness);
    first_input_right[1 + RANDOMNESS_LEN_FE..].copy_from_slice(&make_tweak(TWEAK_TYPE_ENCODING, 0, slot));
    let pre_compressed =
        poseidon16_compress_with_trace(message[..8].try_into().unwrap(), first_input_right, poseidon_16_trace);

    let mut pp_input = [F::default(); 8];
    pp_input[..PUBLIC_PARAM_LEN_FE].copy_from_slice(&xmss_pub_key.public_param);
    let compressed = poseidon16_compress_with_trace(pre_compressed, pp_input, poseidon_16_trace);

    if compressed.iter().any(|&kb| kb == -F::ONE) {
        // ensures uniformity of encoding
        return None;
    }
    let all_indices: Vec<_> = compressed
        .iter()
        .flat_map(|kb| to_little_endian_bits(kb.to_usize(), 24))
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
    // First V indices must sum to TARGET_SUM
    if encoding[..V].iter().map(|&x| x as usize).sum::<usize>() != TARGET_SUM {
        return false;
    }
    true
}
