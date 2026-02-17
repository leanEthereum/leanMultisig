use crate::{
    challenger::{Challenger, RATE, WIDTH},
    *,
};
use field::PrimeCharacteristicRing;
use field::{ExtensionField, PrimeField64};
use symetric::Permutation;

#[derive(Debug)]
pub struct VerifierState<EF: ExtensionField<PF<EF>>, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    index: usize,
    _extension_field: std::marker::PhantomData<EF>,
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    #[must_use]
    pub fn new(transcript: Vec<PF<EF>>, permutation: P) -> Self {
        assert!(EF::DIMENSION <= RATE);
        Self {
            challenger: Challenger::new(permutation),
            transcript,
            index: 0,
            _extension_field: std::marker::PhantomData,
        }
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for VerifierState<EF, P>
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

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> FSVerifier<EF> for VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn state(&self) -> String {
        format!(
            "state {} (len: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.index
        )
    }

    fn transcript(&self) -> Vec<PF<EF>> {
        self.transcript.clone()
    }

    fn next_base_scalars_vec(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        let n_padded = n.next_multiple_of(RATE);
        if n_padded > self.transcript.len() - self.index {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.index..][..n].to_vec();
        if self.transcript[self.index + n..self.index + n_padded]
            .iter()
            .any(|&x| x != PF::<EF>::ZERO)
        {
            return Err(ProofError::InvalidPadding);
        }
        self.index += n_padded;
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [PF::<EF>::ZERO; RATE];
            for (i, val) in chunk.iter().enumerate() {
                buffer[i] = *val;
            }
            self.challenger.observe(buffer);
        }

        Ok(scalars)
    }

    fn receive_hint_base_scalars(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        if n > self.transcript.len() - self.index {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.index..self.index + n].to_vec();
        self.index += n;
        Ok(scalars)
    }

    fn check_pow_grinding(&mut self, bits: usize) -> Result<(), ProofError> {
        if bits == 0 {
            return Ok(());
        }

        if self.index + RATE > self.transcript.len() {
            return Err(ProofError::ExceededTranscript);
        }

        let witness = self.transcript[self.index];
        if self.transcript[self.index + 1..self.index + RATE]
            .iter()
            .any(|&x| x != PF::<EF>::ZERO)
        {
            return Err(ProofError::InvalidPadding);
        }
        self.index += RATE;

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
