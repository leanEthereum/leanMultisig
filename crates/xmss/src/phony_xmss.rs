use multilinear_toolkit::prelude::*;
use rand::{Rng, SeedableRng, rngs::StdRng};
use crate::*;

// Only 1 WOTS, everything else in the merkle tree is random
// Useful for benchmark with a big lifetime, to speed up keys generation

#[derive(Debug)]
struct PhonyXmssSecretKey {
    wots_secret_key: WotsSecretKey,
    first_slot: usize,
    signature_slot: usize,
    merkle_path: Vec<Digest>,
    public_key: XmssPublicKey,
}

impl PhonyXmssSecretKey {
    fn random(rng: &mut impl Rng, first_slot: usize, log_lifetime: usize, signature_slot: usize) -> Self {
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
                first_slot,
            },
        }
    }

    fn sign(&self, message_hash: &Digest, rng: &mut impl Rng) -> XmssSignature {
        let wots_signature = self.wots_secret_key.sign(message_hash, rng);
        XmssSignature {
            wots_signature,
            merkle_proof: self.merkle_path.clone(),
            slot: self.signature_slot,
        }
    }
}

pub fn generate_phony_xmss_signatures(
    log_lifetimes: &[usize],
    message_hash: Digest,
    first_slot: usize,
) -> (Vec<XmssPublicKey>, Vec<XmssSignature>) {
    log_lifetimes
        .par_iter()
        .enumerate()
        .map(|(i, &log_lifetime)| {
            let mut rng = StdRng::seed_from_u64(i as u64);
            let signature_index = rng.random_range(first_slot..first_slot + (1 << log_lifetime));
            let xmss_secret_key = PhonyXmssSecretKey::random(&mut rng, first_slot, log_lifetime, signature_index);
            let signature = xmss_secret_key.sign(&message_hash, &mut rng);
            (xmss_secret_key.public_key, signature)
        })
        .unzip()
}
