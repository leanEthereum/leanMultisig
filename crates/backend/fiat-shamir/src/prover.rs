use crate::{
    MerklePaths, PrunedMerklePaths,
    challenger::{CAPACITY, Challenger, RATE, WIDTH},
    *,
};
use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use field::integers::QuotientMap;
use field::{ExtensionField, PrimeField64};
use koala_bear::symmetric::Permutation;
use rayon::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;
use std::{fmt::Debug, sync::Mutex, time::Instant};

static POW_GRINDING_NANOS: AtomicU64 = AtomicU64::new(0);

pub fn pow_grinding_time() -> Duration {
    Duration::from_nanos(POW_GRINDING_NANOS.load(Ordering::Relaxed))
}

pub fn reset_pow_grinding_time() {
    POW_GRINDING_NANOS.store(0, Ordering::Relaxed);
}

#[derive(Debug)]
pub struct ProverState<EF: ExtensionField<PF<EF>>, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    merkle_paths: Vec<PrunedMerklePaths<PF<EF>, PF<EF>>>,
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> ProverState<EF, P>
where
    PF<EF>: PrimeField64,
{
    #[must_use]
    pub fn new(permutation: P) -> Self {
        assert!(EF::DIMENSION <= RATE);
        Self {
            challenger: Challenger::new(permutation),
            transcript: Vec::new(),
            merkle_paths: Vec::new(),
        }
    }

    pub fn into_proof(self) -> Proof<PF<EF>> {
        Proof {
            transcript: self.transcript,
            merkle_paths: self.merkle_paths,
        }
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for ProverState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn sample_vec(&mut self, len: usize) -> Vec<EF> {
        sample_vec(&mut self.challenger, len)
    }

    fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        self.challenger.sample_in_range(bits, n_samples)
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]> + Permutation<[<PF<EF> as Field>::Packing; WIDTH]>>
    FSProver<EF> for ProverState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn add_base_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
        self.transcript.extend_from_slice(scalars);
    }

    fn observe_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
    }

    fn duplex(&mut self) {
        self.challenger.duplex();
    }

    fn state(&self) -> String {
        format!(
            "state: {} (n_items: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript.len()
        )
    }

    fn add_sumcheck_polynomial(&mut self, coeffs: &[EF], eq_alpha: Option<EF>) {
        match eq_alpha {
            None => {
                let scalars = flatten_scalars_to_base(coeffs);
                self.challenger.observe_many(&scalars);
                self.transcript.extend_from_slice(&scalars[EF::DIMENSION..]); // c0 reconstructed by verifier from claimed_sum
            }
            Some(alpha) => {
                let bare_scalars = flatten_scalars_to_base(coeffs);
                let full_scalars = flatten_scalars_to_base(&expand_bare_to_full(coeffs, alpha));
                self.challenger.observe_many(&full_scalars);
                self.transcript.extend_from_slice(&bare_scalars[EF::DIMENSION..]); // h0 reconstructed by verifier from claimed_sum
            }
        }
    }

    fn hint_merkle_paths_base(&mut self, paths: Vec<MerklePath<PF<EF>, PF<EF>>>) {
        self.merkle_paths.push(MerklePaths(paths).prune());
    }

    fn pow_grinding(&mut self, bits: usize) {
        assert!(bits < PF::<EF>::bits());

        if bits == 0 {
            return;
        }

        let time = Instant::now();

        type Packed<EF> = <PF<EF> as Field>::Packing;
        let lanes = Packed::<EF>::WIDTH;

        let witness_found = Mutex::<Option<PF<EF>>>::new(None);
        // each batch tests lanes witnesses simultaneously
        let num_batches = PF::<EF>::ORDER_U64.div_ceil(lanes as u64);
        (0..num_batches)
            .into_par_iter()
            .find_any(|&batch| {
                let base = batch * lanes as u64;

                let packed_witnesses = Packed::<EF>::from_fn(|lane| {
                    let candidate = base + lane as u64;
                    assert!(candidate < PF::<EF>::ORDER_U64);
                    unsafe { PF::<EF>::from_canonical_unchecked(candidate) }
                });

                let mut packed_state = [Packed::<EF>::ZERO; WIDTH];
                for (slot, val) in packed_state[..CAPACITY]
                    .iter_mut()
                    .zip(&self.challenger.state[..CAPACITY])
                {
                    *slot = Packed::<EF>::from(*val);
                }
                packed_state[CAPACITY] = packed_witnesses;

                self.challenger.permutation.permute_mut(&mut packed_state);

                let samples = packed_state[CAPACITY].as_slice();
                for (sample, witness) in samples.iter().zip(packed_witnesses.as_slice()) {
                    let rand_usize = sample.as_canonical_u64() as usize;
                    if (rand_usize & ((1 << bits) - 1)) == 0 {
                        *witness_found.lock().unwrap() = Some(*witness);
                        return true;
                    }
                }
                false
            })
            .expect("failed to find witness");

        let witness = witness_found.lock().unwrap().unwrap();

        self.challenger.observe_many(&[witness]);
        assert!(self.challenger.state[CAPACITY].as_canonical_u64() & ((1 << bits) - 1) == 0);
        self.transcript.push(witness);

        let elapsed = time.elapsed();
        POW_GRINDING_NANOS.fetch_add(elapsed.as_nanos() as u64, Ordering::Relaxed);
    }
}
