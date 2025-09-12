use rand::Rng;

use crate::*;

#[derive(Debug)]
pub struct XmssSecretKey<const LOG_LIFETIME: usize> {
    pub wots_secret_keys: Vec<WotsSecretKey>,
    pub merkle_tree: Vec<Vec<Digest>>,
}

#[derive(Debug)]
pub struct XmssSignature {
    pub wots_signature: WotsSignature,
    pub merkle_proof: Vec<(bool, Digest)>,
}

#[derive(Debug)]
pub struct XmssPublicKey<const LOG_LIFETIME: usize>(pub Digest);

impl<const LOG_LIFETIME: usize> XmssSecretKey<LOG_LIFETIME> {
    pub fn random(rng: &mut impl Rng) -> Self {
        let wots_secret_keys: Vec<_> = (0..1 << LOG_LIFETIME)
            .map(|_| WotsSecretKey::random(rng))
            .collect();

        let leaves = wots_secret_keys
            .iter()
            .map(|w| w.public_key().hash())
            .collect::<Vec<_>>();
        let mut merkle_tree = vec![leaves];
        for _ in 0..LOG_LIFETIME {
            let mut next_level = Vec::new();
            let current_level = merkle_tree.last().unwrap();
            for (left, right) in current_level.chunks(2).map(|chunk| (chunk[0], chunk[1])) {
                next_level.push(poseidon16_compress(&left, &right));
            }
            merkle_tree.push(next_level);
        }
        Self {
            wots_secret_keys,
            merkle_tree,
        }
    }

    pub fn sign(&self, message_hash: &Digest, index: usize, rng: &mut impl Rng) -> XmssSignature {
        assert!(
            index < (1 << LOG_LIFETIME),
            "Index out of bounds for XMSS signature"
        );
        let wots_signature = self.wots_secret_keys[index].sign(message_hash, rng);
        let merkle_proof = (0..LOG_LIFETIME)
            .scan(index, |current_idx, level| {
                let is_left = *current_idx % 2 == 0;
                let neighbour_index = *current_idx ^ 1;
                let neighbour = self.merkle_tree[level][neighbour_index];
                // Move up to the next level.
                *current_idx /= 2;
                Some((is_left, neighbour))
            })
            .collect();
        XmssSignature {
            wots_signature,
            merkle_proof,
        }
    }

    pub fn public_key(&self) -> XmssPublicKey<LOG_LIFETIME> {
        XmssPublicKey(self.merkle_tree.last().unwrap()[0])
    }
}

impl<const LOG_LIFETIME: usize> XmssPublicKey<LOG_LIFETIME> {
    pub fn verify(&self, message_hash: &Digest, signature: &XmssSignature) -> bool {
        let Some(wots_public_key) = signature
            .wots_signature
            .recover_public_key(message_hash, &signature.wots_signature)
        else {
            return false;
        };
        // merkle root verification
        let mut current_hash = wots_public_key.hash();
        if signature.merkle_proof.len() != LOG_LIFETIME {
            return false;
        }
        for (is_left, neighbour) in &signature.merkle_proof {
            if *is_left {
                current_hash = poseidon16_compress(&current_hash, neighbour)
            } else {
                current_hash = poseidon16_compress(neighbour, &current_hash);
            }
        }
        current_hash == self.0
    }
}
