use rand::Rng;

use crate::*;

// Only 1 WOTS, everything else in the merkle tree is random
// Useful for benchmark with a big lifetime, to speed up keys generation

#[derive(Debug)]
pub struct PhonyXmssSecretKey<const LOG_LIFETIME: usize> {
    pub wots_secret_key: WotsSecretKey,
    pub signature_index: usize,
    pub merkle_path: Vec<Digest>,
    pub public_key: XmssPublicKey<LOG_LIFETIME>,
}

impl<const LOG_LIFETIME: usize> PhonyXmssSecretKey<LOG_LIFETIME> {
    pub fn random(rng: &mut impl Rng, signature_index: usize) -> Self {
        assert!(
            signature_index < (1 << LOG_LIFETIME),
            "Index out of bounds for XMSS signature"
        );
        let wots_secret_key = WotsSecretKey::random(rng);
        let mut merkle_path = Vec::new();
        let mut hash = wots_secret_key.public_key().hash();
        for i in 0..LOG_LIFETIME {
            let phony_neighbour: Digest = rng.random();
            let is_left = (signature_index >> i).is_multiple_of(2);
            if is_left {
                hash = poseidon16_compress(&hash, &phony_neighbour);
            } else {
                hash = poseidon16_compress(&phony_neighbour, &hash);
            };
            merkle_path.push(phony_neighbour);
        }
        Self {
            wots_secret_key,
            signature_index,
            merkle_path,
            public_key: XmssPublicKey(hash),
        }
    }

    pub fn sign(&self, message_hash: &Digest, rng: &mut impl Rng) -> XmssSignature {
        let wots_signature = self.wots_secret_key.sign(message_hash, rng);
        XmssSignature {
            wots_signature,
            merkle_proof: self
                .merkle_path
                .iter()
                .enumerate()
                .map(|(i, h)| {
                    let is_left = (self.signature_index >> i).is_multiple_of(2);
                    (is_left, *h)
                })
                .collect(),
        }
    }
}
