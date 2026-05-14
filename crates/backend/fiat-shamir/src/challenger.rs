use std::marker::PhantomData;

use field::{PrimeField32, PrimeField64};
use sha2::{Digest, Sha256};
use symetric::Compression;

pub(crate) const RATE: usize = 8;
pub(crate) const WIDTH: usize = RATE * 2;

#[derive(Clone, Debug)]
pub struct Challenger<F, P> {
    pub compressor: P,
    pub state: [F; RATE],
}

impl<F: PrimeField64, P: Compression<[F; WIDTH]>> Challenger<F, P> {
    pub fn new(compressor: P) -> Self
    where
        F: Default,
    {
        Self {
            compressor,
            state: [F::ZERO; RATE],
        }
    }

    pub fn observe(&mut self, value: [F; RATE]) {
        self.state = self.compressor.compress({
            let mut concat = [F::ZERO; WIDTH];
            concat[..RATE].copy_from_slice(&self.state);
            concat[RATE..].copy_from_slice(&value);
            concat
        })[..RATE]
            .try_into()
            .unwrap();
    }

    pub fn observe_scalars(&mut self, scalars: &[F]) {
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [F::ZERO; RATE];
            for (i, val) in chunk.iter().enumerate() {
                buffer[i] = *val;
            }
            self.observe(buffer);
        }
    }

    pub fn sample_many(&mut self, n: usize) -> Vec<[F; RATE]> {
        let mut sampled = Vec::with_capacity(n + 1);
        for i in 0..n + 1 {
            let mut domain_sep = [F::ZERO; RATE];
            domain_sep[0] = F::from_usize(i);
            let hashed = self.compressor.compress({
                let mut concat = [F::ZERO; WIDTH];
                concat[..RATE].copy_from_slice(&domain_sep);
                concat[RATE..].copy_from_slice(&self.state);
                concat
            })[..RATE]
                .try_into()
                .unwrap();
            sampled.push(hashed);
        }
        self.state = sampled.pop().unwrap();
        sampled
    }

    /// Warning: not perfectly uniform
    pub fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        assert!(bits < F::bits());
        let sampled_fe = self.sample_many(n_samples.div_ceil(RATE)).into_iter().flatten();
        let mut res = Vec::new();
        for fe in sampled_fe.take(n_samples) {
            let rand_usize = fe.as_canonical_u64() as usize;
            res.push(rand_usize & ((1 << bits) - 1));
        }
        res
    }
}

#[derive(Clone, Debug)]
pub struct ChallengerSha2<F> {
    pub sha2: Sha256,
    _marker: PhantomData<F>,
}

impl<F: PrimeField32> ChallengerSha2<F> {
    pub fn new() -> Self {
        Self {
            sha2: Sha256::new(),
            _marker: PhantomData,
        }
    }

    pub fn observe(&mut self, value: [F; RATE]) {
        for val in value {
            self.sha2.update(val.as_canonical_u32().to_le_bytes());
        }
    }

    pub fn observe_scalars(&mut self, scalars: &[F]) {
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [F::ZERO; RATE];
            for (i, val) in chunk.iter().enumerate() {
                buffer[i] = *val;
            }
            self.observe(buffer);
        }
    }

    pub fn observe_bytes(&mut self, bytes: &[u8]) {
        self.sha2.update(bytes);
    }

    pub fn sample_many(&mut self, n: usize) -> Vec<[F; RATE]> {
        let mut sampled = Vec::with_capacity(n + 1);
        for i in 0..n + 1 {
            sampled.push(self.sample_chunk(i));
        }
        let last = sampled.pop().unwrap();
        self.sha2 = Sha256::new();
        self.observe(last);
        sampled
    }

    pub fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        assert!(bits < F::bits());
        let sampled_fe = self.sample_many(n_samples.div_ceil(RATE)).into_iter().flatten();
        let mut res = Vec::new();
        for fe in sampled_fe.take(n_samples) {
            let rand_usize = fe.as_canonical_u64() as usize;
            res.push(rand_usize & ((1 << bits) - 1));
        }
        res
    }

    pub fn pow_grinding_sample_matches(&self, bits: usize) -> bool {
        assert!(bits < F::bits());
        let sample = self.sample_first_word(0, 0);
        let rand_usize = sample.as_canonical_u64() as usize;
        (rand_usize & ((1 << bits) - 1)) == 0
    }

    pub fn pow_grinding_witness_matches(&self, witness: F, bits: usize) -> bool {
        let mut challenger = self.clone();
        challenger.observe_scalars(&[witness]);
        challenger.pow_grinding_sample_matches(bits)
    }

    fn sample_chunk(&self, domain_sep: usize) -> [F; RATE] {
        let mut words = Vec::with_capacity(RATE);
        for block_idx in 0u64.. {
            let digest = self.sample_digest(domain_sep, block_idx);
            for word in digest.chunks_exact(size_of::<u32>()) {
                let word = u32::from_le_bytes(word.try_into().unwrap());
                words.push(F::from_int(word));
                if words.len() == RATE {
                    return words.try_into().unwrap();
                }
            }
        }
        unreachable!()
    }

    fn sample_first_word(&self, domain_sep: usize, block_idx: u64) -> F {
        let digest = self.sample_digest(domain_sep, block_idx);
        let word = u32::from_le_bytes(digest[..size_of::<u32>()].try_into().unwrap());
        F::from_int(word)
    }

    fn sample_digest(&self, domain_sep: usize, block_idx: u64) -> sha2::digest::Output<Sha256> {
        let mut hasher = self.sha2.clone();
        hasher.update((domain_sep as u64).to_le_bytes());
        hasher.update(block_idx.to_le_bytes());
        hasher.finalize()
    }
}

impl<F: PrimeField32> Default for ChallengerSha2<F> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use field::PrimeCharacteristicRing;
    use koala_bear::KoalaBear;

    use super::ChallengerSha2;

    #[test]
    fn sha2_pow_grinding_direct_predicate_matches_sampling_path() {
        let transcript_prefixes = [
            vec![],
            vec![KoalaBear::ONE],
            (0..17).map(KoalaBear::from_usize).collect::<Vec<_>>(),
            (100..141).map(KoalaBear::from_usize).collect::<Vec<_>>(),
        ];

        for prefix in transcript_prefixes {
            let mut challenger = ChallengerSha2::new();
            challenger.observe_scalars(&prefix);

            for bits in 1..=20 {
                for candidate in [0, 1, 2, 3, 5, 8, 13, 21, 55, 89, 144, 233, 377, 610] {
                    let witness = KoalaBear::from_usize(candidate);
                    let mut sampling_path = challenger.clone();
                    sampling_path.observe_scalars(&[witness]);
                    let expected = sampling_path.sample_in_range(bits, 1)[0] == 0;
                    let actual = challenger.pow_grinding_witness_matches(witness, bits);
                    assert_eq!(actual, expected);
                }
            }
        }
    }
}
