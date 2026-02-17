use crate::{
    challenger::{Challenger, RATE, WIDTH},
    *,
};
use field::Field;
use field::PackedValue;
use field::PrimeCharacteristicRing;
use field::integers::QuotientMap;
use field::{ExtensionField, PrimeField64};
use rayon::prelude::*;
use std::{fmt::Debug, sync::Mutex};
use symetric::Compression;

#[derive(Debug)]
pub struct ProverState<EF: ExtensionField<PF<EF>>, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Proof<PF<EF>>,
}

impl<EF: ExtensionField<PF<EF>>, P: Compression<[PF<EF>; WIDTH]>> ProverState<EF, P>
where
    PF<EF>: PrimeField64,
{
    #[must_use]
    pub fn new(compressor: P) -> Self {
        assert!(EF::DIMENSION <= RATE);
        Self {
            challenger: Challenger::new(compressor),
            transcript: Proof(Vec::new()),
        }
    }

    pub fn raw_proof(&self) -> Vec<PF<EF>> {
        self.transcript.raw_proof()
    }

    pub fn pruned_proof(&self) -> PrunedProof<PF<EF>> {
        self.transcript.clone().prune()
    }

    pub fn into_pruned_proof(self) -> PrunedProof<PF<EF>> {
        self.transcript.prune()
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Compression<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for ProverState<EF, P>
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

impl<EF: ExtensionField<PF<EF>>, P: Compression<[PF<EF>; WIDTH]> + Compression<[<PF<EF> as Field>::Packing; WIDTH]>>
    FSProver<EF> for ProverState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn add_base_scalars(&mut self, scalars: &[PF<EF>]) {
        self.transcript.0.push(TranscriptData::Interraction(scalars.to_vec()));
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [PF::<EF>::ZERO; RATE];
            for (i, val) in chunk.iter().enumerate() {
                buffer[i] = *val;
            }
            self.challenger.observe(buffer);
        }
    }

    fn state(&self) -> String {
        format!(
            "state: {} (len: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript.raw_proof().len()
        )
    }

    fn hint_merkle_paths_base(&mut self, paths: Vec<MerklePath<PF<EF>, PF<EF>>>) {
        self.transcript.0.push(TranscriptData::MerklePaths(MerklePaths(paths)));
    }

    fn pow_grinding(&mut self, bits: usize) {
        assert!(bits < PF::<EF>::bits());

        if bits == 0 {
            return;
        }

        type Packed<EF> = <PF<EF> as Field>::Packing;
        let lanes = Packed::<EF>::WIDTH;

        let witness_found = Mutex::<Option<PF<EF>>>::new(None);
        // each batch tests lanes witnesses simultaneously
        let num_batches = (PF::<EF>::ORDER_U64 + lanes as u64 - 1) / lanes as u64;
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
                packed_state[..RATE]
                    .iter_mut()
                    .zip(&self.challenger.state)
                    .for_each(|(val, state)| *val = Packed::<EF>::from(*state));
                packed_state[RATE] = packed_witnesses;

                self.challenger.compressor.compress_mut(&mut packed_state);

                let samples = packed_state[0].as_slice();
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

        let witness_found = witness_found.lock().unwrap().unwrap();

        self.challenger.observe({
            let mut value = [PF::<EF>::ZERO; RATE];
            value[0] = witness_found;
            value
        });
        assert!(self.challenger.state[0].as_canonical_u64() & ((1 << bits) - 1) == 0);
        self.transcript.0.push(TranscriptData::GrindingWitness(witness_found));
    }
}
