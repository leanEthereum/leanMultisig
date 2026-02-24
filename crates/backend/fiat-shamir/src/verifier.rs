use crate::{
    challenger::{Challenger, RATE, WIDTH},
    *,
};
use field::PrimeCharacteristicRing;
use field::{ExtensionField, PrimeField64};
use symetric::Compression;

#[derive(Debug)]
pub struct VerifierState<EF: ExtensionField<PF<EF>>, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    merkle_openings: Vec<MerkleOpening<PF<EF>>>,
    transcript_index: usize,
    merkle_opening_index: usize,
    _extension_field: std::marker::PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, P: Compression<[PF<EF>; WIDTH]>> VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    #[must_use]
    pub fn new(raw_proof: RawProof<PF<EF>>, compressor: P) -> Self {
        assert!(EF::DIMENSION <= RATE);
        Self {
            challenger: Challenger::new(compressor),
            transcript: raw_proof.transcript,
            merkle_openings: raw_proof.merkle_openings,
            transcript_index: 0,
            merkle_opening_index: 0,
            _extension_field: std::marker::PhantomData,
        }
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Compression<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for VerifierState<EF, P>
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

impl<EF: ExtensionField<PF<EF>>, P: Compression<[PF<EF>; WIDTH]>> FSVerifier<EF> for VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn state(&self) -> String {
        format!(
            "state {} (transcript_idx: {}, merkle_opening_idx: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript_index,
            self.merkle_opening_index,
        )
    }

    fn next_base_scalars_vec(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        let n_padded = n.next_multiple_of(RATE);
        if n_padded > self.transcript.len() - self.transcript_index {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.transcript_index..][..n].to_vec();
        if self.transcript[self.transcript_index + n..self.transcript_index + n_padded]
            .iter()
            .any(|&x| x != PF::<EF>::ZERO)
        {
            return Err(ProofError::InvalidPadding);
        }
        self.transcript_index += n_padded;
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [PF::<EF>::ZERO; RATE];
            for (i, val) in chunk.iter().enumerate() {
                buffer[i] = *val;
            }
            self.challenger.observe(buffer);
        }

        Ok(scalars)
    }

    fn next_merkle_opening(&mut self) -> Result<MerkleOpening<PF<EF>>, ProofError> {
        if self.merkle_opening_index >= self.merkle_openings.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let opening = self.merkle_openings[self.merkle_opening_index].clone();
        self.merkle_opening_index += 1;
        Ok(opening)
    }

    fn check_pow_grinding(&mut self, bits: usize) -> Result<(), ProofError> {
        if bits == 0 {
            return Ok(());
        }

        if self.transcript_index + RATE > self.transcript.len() {
            return Err(ProofError::ExceededTranscript);
        }

        let witness = self.transcript[self.transcript_index];
        if self.transcript[self.transcript_index + 1..self.transcript_index + RATE]
            .iter()
            .any(|&x| x != PF::<EF>::ZERO)
        {
            return Err(ProofError::InvalidPadding);
        }
        self.transcript_index += RATE;

        self.challenger.observe({
            let mut value = [PF::<EF>::ZERO; RATE];
            value[0] = witness;
            value
        });
        if self.challenger.state[0].as_canonical_u64() & ((1 << bits) - 1) != 0 {
            return Err(ProofError::InvalidGrindingWitness);
        }
        Ok(())
    }
}
