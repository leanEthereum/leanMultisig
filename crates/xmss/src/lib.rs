#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use p3_koala_bear::KoalaBear;
use p3_symmetric::Permutation;
use rand::Rng;
use utils::{Poseidon16, Poseidon24};

type F = KoalaBear;
pub type Digest = [F; 8];
pub type Message = [u8; N_CHAINS]; // each value is < CHAIN_LOG_LENGTH

pub const N_CHAINS: usize = 64;
pub const CHAIN_LOG_LENGTH: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << CHAIN_LOG_LENGTH;

pub const XMSS_MERKLE_HEIGHT: usize = 5;

#[derive(Debug)]
pub struct WotsSecretKey {
    pre_images: [Digest; N_CHAINS],
    public_key: WotsPublicKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WotsPublicKey(pub [Digest; N_CHAINS]);
#[derive(Debug)]
pub struct WotsSignature(pub [Digest; N_CHAINS]);

impl WotsSecretKey {
    pub fn random<R: Rng>(rng: &mut R, poseidon16: &Poseidon16) -> Self {
        let mut pre_images = [Default::default(); N_CHAINS];
        for i in 0..N_CHAINS {
            let mut pre_image = [F::default(); 8];
            for j in 0..8 {
                pre_image[j] = rng.random();
            }
            pre_images[i] = pre_image;
        }
        Self::new(pre_images, poseidon16)
    }

    #[must_use]
    pub fn new(pre_images: [Digest; N_CHAINS], poseidon16: &Poseidon16) -> Self {
        let mut public_key = [Default::default(); N_CHAINS];
        for i in 0..N_CHAINS {
            public_key[i] = iterate_hash(&pre_images[i], CHAIN_LENGTH, poseidon16);
        }
        Self {
            pre_images,
            public_key: WotsPublicKey(public_key),
        }
    }

    #[must_use]
    pub const fn public_key(&self) -> &WotsPublicKey {
        &self.public_key
    }

    #[must_use]
    pub fn sign(&self, message: &Message, poseidon16: &Poseidon16) -> WotsSignature {
        let mut signature = [Default::default(); N_CHAINS];
        for i in 0..N_CHAINS {
            assert!(
                (message[i] as usize) < CHAIN_LENGTH,
                "Message value out of bounds"
            );
            signature[i] = iterate_hash(&self.pre_images[i], message[i] as usize, poseidon16);
        }
        WotsSignature(signature)
    }
}

impl WotsSignature {
    #[must_use]
    pub fn recover_public_key(
        &self,
        message: &Message,
        signature: &Self,
        poseidon16: &Poseidon16,
    ) -> WotsPublicKey {
        let mut public_key = [Default::default(); N_CHAINS];
        for i in 0..N_CHAINS {
            assert!(
                (message[i] as usize) < CHAIN_LENGTH,
                "Message value out of bounds"
            );
            public_key[i] = iterate_hash(
                &signature.0[i],
                CHAIN_LENGTH - message[i] as usize,
                poseidon16,
            );
        }
        WotsPublicKey(public_key)
    }
}

impl WotsPublicKey {
    #[must_use]
    #[allow(clippy::assertions_on_constants)]
    pub fn hash(&self, poseidon24: &Poseidon24) -> Digest {
        assert!(N_CHAINS.is_multiple_of(2), "TODO");
        let mut digest = Default::default();
        for (a, b) in self.0.chunks(2).map(|chunk| (chunk[0], chunk[1])) {
            digest = poseidon24.permute([a, b, digest].concat().try_into().unwrap())[16..24]
                .try_into()
                .unwrap();
        }
        digest
    }
}

#[derive(Debug)]
pub struct XmssSecretKey {
    pub wots_secret_keys: Vec<WotsSecretKey>,
    pub merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub merkle_proof: Vec<(bool, Digest)>,
}

#[derive(Debug)]
pub struct XmssPublicKey {
    pub root: Digest,
}

impl XmssSecretKey {
    #[allow(clippy::tuple_array_conversions)]
    pub fn random<R: Rng>(rng: &mut R, poseidon16: &Poseidon16, poseidon24: &Poseidon24) -> Self {
        let mut wots_secret_keys = Vec::new();
        for _ in 0..1 << XMSS_MERKLE_HEIGHT {
            wots_secret_keys.push(WotsSecretKey::random(rng, poseidon16));
        }
        let leaves = wots_secret_keys
            .iter()
            .map(|w| w.public_key().hash(poseidon24))
            .collect::<Vec<_>>();
        let mut merkle_tree = vec![leaves];
        for _ in 0..XMSS_MERKLE_HEIGHT {
            let mut next_level = Vec::new();
            let current_level = merkle_tree.last().unwrap();
            for (left, right) in current_level.chunks(2).map(|chunk| (chunk[0], chunk[1])) {
                next_level.push(
                    poseidon16.permute([left, right].concat().try_into().unwrap())[0..8]
                        .try_into()
                        .unwrap(),
                );
            }
            merkle_tree.push(next_level);
        }
        Self {
            wots_secret_keys,
            merkle_tree,
        }
    }

    #[must_use]
    pub fn sign(&self, message: &Message, index: usize, poseidon16: &Poseidon16) -> XmssSignature {
        assert!(
            index < (1 << XMSS_MERKLE_HEIGHT),
            "Index out of bounds for XMSS signature"
        );
        let wots_signature = self.wots_secret_keys[index].sign(message, poseidon16);
        let mut merkle_proof = Vec::new();
        let mut current_index = index;
        for level in 0..XMSS_MERKLE_HEIGHT {
            let is_left = current_index.is_multiple_of(2);
            let neighbour_index = if is_left {
                current_index + 1
            } else {
                current_index - 1
            };
            let neighbour = self.merkle_tree[level][neighbour_index];
            merkle_proof.push((is_left, neighbour));
            current_index /= 2;
        }
        XmssSignature {
            wots_signature,
            merkle_proof,
        }
    }

    #[must_use]
    pub fn public_key(&self) -> XmssPublicKey {
        XmssPublicKey {
            root: self.merkle_tree.last().unwrap()[0],
        }
    }
}

impl XmssPublicKey {
    #[must_use]
    pub fn verify(
        &self,
        message: &Message,
        signature: &XmssSignature,
        poseidon16: &Poseidon16,
        poseidon24: &Poseidon24,
    ) -> bool {
        let wots_public_key = signature.wots_signature.recover_public_key(
            message,
            &signature.wots_signature,
            poseidon16,
        );
        // merkle root verification
        let mut current_hash = wots_public_key.hash(poseidon24);
        if signature.merkle_proof.len() != XMSS_MERKLE_HEIGHT {
            return false;
        }
        for (is_left, neighbour) in &signature.merkle_proof {
            if *is_left {
                current_hash = poseidon16
                    .permute([current_hash, *neighbour].concat().try_into().unwrap())
                    [0..8]
                    .try_into()
                    .unwrap();
            } else {
                current_hash = poseidon16
                    .permute([*neighbour, current_hash].concat().try_into().unwrap())
                    [0..8]
                    .try_into()
                    .unwrap();
            }
        }
        current_hash == self.root
    }
}

fn iterate_hash(a: &Digest, n: usize, poseidon16: &Poseidon16) -> Digest {
    let mut res = *a;
    for _ in 0..n {
        res = poseidon16.permute([res, Default::default()].concat().try_into().unwrap())[0..8]
            .try_into()
            .unwrap();
    }
    res
}

pub fn random_message<R: Rng>(rng: &mut R) -> Message {
    let mut message = [0u8; N_CHAINS];
    for i in 0..N_CHAINS {
        message[i] = rng.random_range(0..CHAIN_LENGTH) as u8;
    }
    message
}

#[cfg(test)]
mod tests {
    use rand::{SeedableRng, rngs::StdRng};
    use utils::{build_poseidon16, build_poseidon24};

    use super::*;

    #[test]
    fn test_wots_signature() {
        let mut rng = StdRng::seed_from_u64(0);
        let poseidon16 = build_poseidon16();
        let sk = WotsSecretKey::random(&mut rng, &poseidon16);
        let message = random_message(&mut rng);
        let signature = sk.sign(&message, &poseidon16);
        assert_eq!(
            signature.recover_public_key(&message, &signature, &poseidon16),
            *sk.public_key()
        );
    }

    #[test]
    fn test_xmss_signature() {
        let mut rng = StdRng::seed_from_u64(0);
        let poseidon16 = build_poseidon16();
        let poseidon24 = build_poseidon24();
        let sk = XmssSecretKey::random(&mut rng, &poseidon16, &poseidon24);
        let message = random_message(&mut rng);
        let index = rng.random_range(0..(1 << XMSS_MERKLE_HEIGHT));
        let signature = sk.sign(&message, index, &poseidon16);
        let public_key = sk.public_key();
        assert!(public_key.verify(&message, &signature, &poseidon16, &poseidon24));
    }
}
