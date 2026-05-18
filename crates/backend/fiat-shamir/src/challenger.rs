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

    /// Samples uniformly random values in `[0, 2^bits)` using rejection sampling.
    ///
    /// Field elements are uniform in `[0, ORDER_U64)`. To avoid modulo bias when
    /// extracting `bits`-wide integers, we reject elements `>= floor(ORDER / 2^bits) * 2^bits`.
    pub fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        assert!(bits < F::bits());
        let mask = (1usize << bits) - 1;
        let threshold = (F::ORDER_U64 >> bits) << bits;
        let mut res = Vec::with_capacity(n_samples);
        while res.len() < n_samples {
            let needed = n_samples - res.len();
            for fe in self.sample_many(needed.div_ceil(RATE)).into_iter().flatten() {
                let x = fe.as_canonical_u64();
                if x < threshold {
                    res.push((x as usize) & mask);
                    if res.len() == n_samples {
                        break;
                    }
                }
            }
        }
        res
    }
}
