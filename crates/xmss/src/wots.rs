use multilinear_toolkit::prelude::*;
use rand::{CryptoRng, Rng};
use utils::{ToUsize, poseidon16_compress_pair, to_little_endian_bits};

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
        self.recover_public_key_with_poseidon_trace(message, slot, xmss_pub_key, signature, &mut Vec::new())
    }

    pub fn recover_public_key_with_poseidon_trace(
        &self,
        message: &[F; MESSAGE_LEN_FE],
        slot: u32,
        xmss_pub_key: &XmssPublicKey,
        signature: &Self,
        poseidon_16_trace: &mut Vec<([F; 16], [F; 8])>,
    ) -> Option<WotsPublicKey> {
        let encoding =
            wots_encode_with_poseidon_trace(message, slot, xmss_pub_key, &signature.randomness, poseidon_16_trace)?;
        Some(WotsPublicKey(std::array::from_fn(|i| {
            iterate_hash_with_poseidon_trace(
                &self.chain_tips[i],
                CHAIN_LENGTH - 1 - encoding[i] as usize,
                poseidon_16_trace,
                xmss_pub_key.public_param,
                slot,
                i,
                encoding[i] as usize,
            )
        })))
    }
}

impl WotsPublicKey {
    pub fn hash(&self, public_param: PublicParam, slot: u32) -> Digest {
        self.hash_with_poseidon_trace(&mut Vec::new(), public_param, slot)
    }

    pub fn hash_with_poseidon_trace(
        &self,
        poseidon_16_trace: &mut Poseidon16History,
        public_param: PublicParam,
        slot: u32,
    ) -> Digest {
        let left = build_left(&public_param, &self.0[0]);
        let right = build_right(make_tweak(TWEAK_TYPE_WOTS_PK, 0, slot), &self.0[1]);
        let mut running_hash: Digest = poseidon16_compress_with_trace(left, right, poseidon_16_trace)[..DIGEST_SIZE]
            .try_into()
            .unwrap();
        for i in 2..V {
            let left = build_left(&public_param, &running_hash);
            let right = build_right(make_tweak(TWEAK_TYPE_WOTS_PK, i - 1, slot), &self.0[i]);
            running_hash = poseidon16_compress_with_trace(left, right, poseidon_16_trace)[..DIGEST_SIZE]
                .try_into()
                .unwrap();
        }
        running_hash
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
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left(&public_param, &acc);
        let right = build_right(tweak, &Default::default());
        poseidon16_compress_pair(left, right)[..DIGEST_SIZE].try_into().unwrap()
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
    (0..n).fold(*a, |acc, j| {
        let tweak = make_tweak(TWEAK_TYPE_CHAIN, chain_index * CHAIN_LENGTH + start_step + j, slot);
        let left = build_left(&public_param, &acc);
        let right = build_right(tweak, &Default::default());
        poseidon16_compress_with_trace(left, right, poseidon_16_trace)[..DIGEST_SIZE]
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

    let compressed = poseidon16_compress_with_trace(pre_compressed, xmss_pub_key.flaten(), poseidon_16_trace);

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

