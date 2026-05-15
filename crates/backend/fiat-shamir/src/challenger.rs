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

    /// Absorbs scalars into the sponge, `RATE - 1` (= 7) per permutation.
    ///
    /// Each permutation compresses `[-1, <=7 scalars] || state`: the leading `-1`
    /// in the first slot is a domain separator. `sample_many` puts separators
    /// `0..=n` in that same slot, so an observe input can never collide with a
    /// sample input.
    pub fn observe_scalars(&mut self, scalars: &[F]) {
        for chunk in scalars.chunks(RATE - 1) {
            let mut input = [F::ZERO; WIDTH];
            input[0] = -F::ONE;
            input[1..1 + chunk.len()].copy_from_slice(chunk);
            input[RATE..].copy_from_slice(&self.state);
            self.state = self.compressor.compress(input)[..RATE].try_into().unwrap();
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
