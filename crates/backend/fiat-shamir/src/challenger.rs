use field::PrimeField64;
use koala_bear::symmetric::Permutation;

pub(crate) const RATE: usize = 8;
pub(crate) const WIDTH: usize = RATE * 2;
pub(crate) const CAPACITY: usize = WIDTH - RATE;

#[derive(Clone, Debug)]
pub struct Challenger<F, P> {
    pub permutation: P,
    pub state: [F; WIDTH],
    rate_fresh: bool,
}

impl<F: PrimeField64, P: Permutation<[F; WIDTH]>> Challenger<F, P> {
    pub fn new(permutation: P) -> Self
    where
        F: Default,
    {
        Self {
            permutation,
            state: [F::ZERO; WIDTH],
            rate_fresh: false,
        }
    }

    pub fn observe(&mut self, value: [F; RATE]) {
        self.state[CAPACITY..].copy_from_slice(&value);
        self.permutation.permute_mut(&mut self.state);
        self.rate_fresh = true;
    }

    pub fn observe_many(&mut self, scalars: &[F]) {
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [F::ZERO; RATE];
            buffer[..chunk.len()].copy_from_slice(chunk);
            self.observe(buffer);
        }
    }

    pub fn duplex(&mut self) {
        self.observe([F::ZERO; RATE]);
    }

    pub fn sample(&mut self) -> [F; RATE] {
        assert!(self.rate_fresh, "stale rate. insert a duplex() before.");
        let out: [F; RATE] = self.state[CAPACITY..].try_into().unwrap();
        self.rate_fresh = false;
        out
    }

    pub fn sample_many(&mut self, n: usize) -> Vec<[F; RATE]> {
        if n == 0 {
            return Vec::new();
        }
        let mut out = Vec::with_capacity(n);
        out.push(self.sample());
        for _ in 1..n {
            self.duplex();
            out.push(self.sample());
        }
        out
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
