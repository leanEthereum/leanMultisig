use backend::*;
use rand::{CryptoRng, RngExt};
use serde::{Deserialize, Serialize};
use utils::poseidon8_compress_pair;

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
    // We use a T-Sponge with replacement, i.e. we use Poseidon in compression mode + replace (instead of modular addition) when ingesting 4 new field elements.
    pub fn hash(&self, public_param: PublicParam, slot: u32) -> Digest {
        // IV: [tweak(1) | 0 | pp(2)]
        let tweak = make_tweak(TWEAK_TYPE_WOTS_PK, 0, slot);
        let mut state = [F::default(); DIGEST_LEN_FE];
        state[..TWEAK_LEN].copy_from_slice(&tweak);
        // state[1..2] = 0 (default)
        state[DIGEST_LEN_FE - PUBLIC_PARAM_LEN_FE..].copy_from_slice(&public_param);

        let zeros = [F::ZERO; DIGEST_LEN_FE]; // for snark-friendliness (not necessary for security)
        state = poseidon8_compress_pair(&state, &zeros);

        for i in (0..V).step_by(2) {
            let mut chunk = [F::default(); DIGEST_LEN_FE];
            chunk[..XMSS_DIGEST_LEN].copy_from_slice(&self.0[i]);
            chunk[XMSS_DIGEST_LEN..].copy_from_slice(&self.0[i + 1]);
            state = poseidon8_compress_pair(&state, &chunk);
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
    // Chain hash layout: left = [tweak (1) | zero (1) | data (2)], right = [public_param(2) | zeros(2)].
    let right = build_right_chain_input(&public_param);
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left_chain_input(tweak, &acc);
        poseidon8_compress_pair(&left, &right)[..XMSS_DIGEST_LEN]
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

// Each encoding FE is decomposed into `CHUNKS_PER_FE` chunks of `W` bits.
// W = 3, CHUNKS_PER_FE = 21 → 63 bits used per Goldilocks element, 1-bit slack
// (verifier asserts it's 0 or 1, factored as (diff)·(diff − 2^63) = 0).
// Total chunks across all 4 output FE: 4 × 21 = 84, of which the first V = 42
// are used as Winternitz indices.
const CHUNKS_PER_FE: usize = 21;
const _: () = assert!(CHUNKS_PER_FE * W <= 63); // 1-bit slack
const _: () = assert!(DIGEST_LEN_FE * CHUNKS_PER_FE >= V);

pub fn wots_encode(
    message: &[F; MESSAGE_LEN_FE],
    slot: u32,
    xmss_pub_key: &XmssPublicKey,
    randomness: &Randomness,
) -> Option<[u8; V]> {
    let first_input_left = message;
    let mut first_input_right = [F::default(); DIGEST_LEN_FE];
    first_input_right[..RANDOMNESS_LEN_FE].copy_from_slice(randomness);
    first_input_right[RANDOMNESS_LEN_FE..][..TWEAK_LEN].copy_from_slice(&make_tweak(TWEAK_TYPE_ENCODING, 0, slot));
    let pre_compressed = poseidon8_compress_pair(first_input_left, &first_input_right);

    let mut second_input_right = [F::default(); DIGEST_LEN_FE];
    second_input_right[..PUBLIC_PARAM_LEN_FE].copy_from_slice(&xmss_pub_key.public_param);
    let compressed = poseidon8_compress_pair(&pre_compressed, &second_input_right);

    let mut all_indices = [0u8; DIGEST_LEN_FE * CHUNKS_PER_FE];
    for (i, g) in compressed.iter().enumerate() {
        let value = g.as_canonical_u64();
        for j in 0..CHUNKS_PER_FE {
            all_indices[i * CHUNKS_PER_FE + j] = ((value >> (j * W)) & ((1u64 << W) - 1)) as u8;
        }
    }
    let used: [u8; V] = all_indices[..V].try_into().unwrap();
    is_valid_encoding(&used).then_some(used)
}

fn is_valid_encoding(encoding: &[u8]) -> bool {
    if encoding.len() != V {
        return false;
    }
    if !encoding.iter().all(|&x| (x as usize) < CHAIN_LENGTH) {
        return false;
    }
    if encoding.iter().map(|&x| x as usize).sum::<usize>() != TARGET_SUM {
        return false;
    }
    true
}
