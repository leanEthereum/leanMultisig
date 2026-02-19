use field::PrimeField64;
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

    fn hash_state_with(&self, value: &[F; RATE]) -> [F; RATE] {
        self.compressor.compress({
            let mut concat = [F::ZERO; WIDTH];
            concat[..RATE].copy_from_slice(&self.state);
            concat[RATE..].copy_from_slice(value);
            concat
        })[..RATE]
            .try_into()
            .unwrap()
    }

    pub fn observe(&mut self, value: [F; RATE]) {
        self.state = self.hash_state_with(&value);
    }

    pub fn sample_many(&mut self, n: usize) -> Vec<[F; RATE]> {
        let mut sampled = Vec::with_capacity(n);
        for i in 0..n + 1 {
            let mut domain_sep = [F::ZERO; RATE];
            domain_sep[0] = F::from_usize(i);
            sampled.push(self.hash_state_with(&domain_sep));
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
