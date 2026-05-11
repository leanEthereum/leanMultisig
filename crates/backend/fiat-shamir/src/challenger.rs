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
