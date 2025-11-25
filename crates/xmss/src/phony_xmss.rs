use rand::Rng;

use crate::*;

// Only 1 WOTS, everything else in the merkle tree is random
// Useful for benchmark with a big lifetime, to speed up keys generation

#[derive(Debug)]
pub struct PhonyXmssSecretKey {
    pub wots_secret_key: WotsSecretKey,
    pub first_slot: usize,
    pub signature_slot: usize,
    pub merkle_path: Vec<Digest>,
    pub public_key: XmssPublicKey,
}

impl PhonyXmssSecretKey {
    pub fn random(rng: &mut impl Rng, first_slot: usize, log_lifetime: usize, signature_slot: usize) -> Self {
        assert!(
            signature_slot.checked_sub(first_slot).unwrap() < (1 << log_lifetime),
            "Index out of bounds for XMSS signature"
        );
        let wots_secret_key = WotsSecretKey::random(rng);
        let mut merkle_path = Vec::new();
        let mut hash = wots_secret_key.public_key().hash();
        let wots_index = signature_slot - first_slot;
        for i in 0..log_lifetime {
            let phony_neighbour: Digest = rng.random();
            let is_left = (wots_index >> i).is_multiple_of(2);
            if is_left {
                hash = poseidon16_compress(&hash, &phony_neighbour);
            } else {
                hash = poseidon16_compress(&phony_neighbour, &hash);
            };
            merkle_path.push(phony_neighbour);
        }
        Self {
            wots_secret_key,
            first_slot,
            signature_slot,
            merkle_path,
            public_key: XmssPublicKey {
                merkle_root: hash,
                log_lifetime,
                first_slot
            },
        }
    }

    pub fn sign(&self, message_hash: &Digest, rng: &mut impl Rng) -> XmssSignature {
        let wots_signature = self.wots_secret_key.sign(message_hash, rng);
        XmssSignature {
            wots_signature,
            merkle_proof: self.merkle_path.clone(),
            slot: self.signature_slot,
        }
    }
}
