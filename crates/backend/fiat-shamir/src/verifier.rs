use std::any::TypeId;
use std::iter::repeat_n;

use crate::{
    MerkleOpening, MerklePaths, PrunedMerklePaths, RawProof,
    challenger::{Challenger, ChallengerSha2, RATE, WIDTH},
    transcript::{DIGEST_LEN_FE, Proof},
    *,
};
use field::PrimeCharacteristicRing;
use field::{ExtensionField, PrimeField32, PrimeField64};
use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
use sha2::{Digest as Sha2DigestTrait, Sha256};
use symetric::Compression;
use symetric::merkle::Sha256Digest;

pub struct VerifierState<EF: ExtensionField<PF<EF>>, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    transcript_offset: usize,
    merkle_openings: Vec<MerkleOpening<PF<EF>>>,
    merkle_opening_index: usize,
    raw_transcript: Vec<PF<EF>>, // reconstructed during the proof verification, it's the format that the zkVM recursion program expects (no Merkle pruning, no sumcheck optimization to send less data, etc)
}

impl<EF: ExtensionField<PF<EF>>, C: Compression<[PF<EF>; WIDTH]>> VerifierState<EF, C>
where
    PF<EF>: PrimeField64,
{
    pub fn new(proof: Proof<PF<EF>>, compressor: C) -> Result<Self, ProofError> {
        if !proof.commitments.is_empty() {
            return Err(ProofError::InvalidProof);
        }

        let mut merkle_openings = Vec::new();
        for paths in proof.merkle_paths {
            let restored = Self::restore_merkle_paths(paths).ok_or(ProofError::InvalidProof)?;
            merkle_openings.extend(restored);
        }

        Ok(Self {
            challenger: Challenger::new(compressor),
            transcript: proof.transcript,
            transcript_offset: 0,
            merkle_openings,
            merkle_opening_index: 0,
            raw_transcript: Vec::new(),
        })
    }

    pub fn into_raw_proof(self) -> RawProof<PF<EF>> {
        RawProof {
            transcript: self.raw_transcript,
            merkle_openings: self.merkle_openings,
        }
    }

    fn absorb_and_record(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_scalars(scalars);
        let total_padded = scalars.len().next_multiple_of(RATE);
        self.raw_transcript.extend_from_slice(scalars);
        self.raw_transcript
            .extend(repeat_n(PF::<EF>::ZERO, total_padded - scalars.len()));
    }

    fn read_transcript(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        if self.transcript_offset + n > self.transcript.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.transcript_offset..self.transcript_offset + n].to_vec();
        self.transcript_offset += n;
        Ok(scalars)
    }

    #[allow(clippy::missing_transmute_annotations)]
    fn restore_merkle_paths(
        paths: PrunedMerklePaths<PF<EF>, [PF<EF>; DIGEST_LEN_FE]>,
    ) -> Option<Vec<MerkleOpening<PF<EF>>>> {
        assert_eq!(TypeId::of::<PF<EF>>(), TypeId::of::<KoalaBear>());
        // SAFETY: We've confirmed PF<EF> == KoalaBear
        let paths: PrunedMerklePaths<KoalaBear, [KoalaBear; DIGEST_LEN_FE]> = unsafe { std::mem::transmute(paths) };
        let perm = default_koalabear_poseidon1_16();
        let hash_fn = |data: &[KoalaBear]| symetric::hash_slice::<_, _, 16, 8, DIGEST_LEN_FE>(&perm, data);
        let combine_fn = |left: &[KoalaBear; DIGEST_LEN_FE], right: &[KoalaBear; DIGEST_LEN_FE]| {
            symetric::compress(&perm, [*left, *right])
        };
        let restored: MerklePaths<KoalaBear, [KoalaBear; DIGEST_LEN_FE]> = paths.restore(&hash_fn, &combine_fn)?;
        let openings: Vec<MerkleOpening<KoalaBear>> = restored
            .0
            .into_iter()
            .map(|path| MerkleOpening {
                leaf_data: path.leaf_data,
                path: path.sibling_hashes,
            })
            .collect();
        // SAFETY: PF<EF> == KoalaBear
        Some(unsafe { std::mem::transmute(openings) })
    }
}

impl<EF: ExtensionField<PF<EF>>, C: Compression<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for VerifierState<EF, C>
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

impl<EF: ExtensionField<PF<EF>>, C: Compression<[PF<EF>; WIDTH]>> FSVerifier<EF> for VerifierState<EF, C>
where
    PF<EF>: PrimeField64,
{
    type Digest = [PF<EF>; DIGEST_LEN_FE];

    fn state(&self) -> String {
        format!(
            "state {} (offset: {}, merkle_idx: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript_offset,
            self.merkle_opening_index,
        )
    }

    fn observe_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_scalars(scalars);
    }

    fn next_base_scalars_vec(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        let scalars = self.read_transcript(n)?;
        self.absorb_and_record(&scalars);
        Ok(scalars)
    }

    fn next_commitment(&mut self) -> Result<Self::Digest, ProofError> {
        self.next_base_scalars_vec(DIGEST_LEN_FE)
            .map(|scalars| scalars.try_into().unwrap())
    }

    fn next_merkle_opening(&mut self) -> Result<MerkleOpening<PF<EF>, Self::Digest>, ProofError> {
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
        let witness = self.read_transcript(1)?[0];
        self.challenger.observe_scalars(&[witness]);
        if self.challenger.state[0].as_canonical_u64() & ((1 << bits) - 1) != 0 {
            return Err(ProofError::InvalidGrindingWitness);
        }
        self.raw_transcript.push(witness);
        self.raw_transcript.extend(repeat_n(PF::<EF>::ZERO, RATE - 1));
        Ok(())
    }

    fn next_sumcheck_polynomial(
        &mut self,
        n_coeffs: usize,
        claimed_sum: EF,
        eq_alpha: Option<EF>,
    ) -> ProofResult<Vec<EF>> {
        match eq_alpha {
            None => {
                let rest_scalars = self.read_transcript((n_coeffs - 1) * EF::DIMENSION)?;
                let rest_coeffs: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                // we use h(0) + h(1) = claimed_sum to recover the missing c0
                let c0 = (claimed_sum - rest_coeffs.iter().copied().sum::<EF>()).halve();

                let mut full_coeffs = Vec::with_capacity(n_coeffs);
                full_coeffs.push(c0);
                full_coeffs.extend_from_slice(&rest_coeffs);

                let mut all_scalars = flatten_scalars_to_base(&[c0]);
                all_scalars.extend_from_slice(&rest_scalars);
                self.absorb_and_record(&all_scalars);
                Ok(full_coeffs)
            }
            Some(alpha) => {
                let rest_scalars = self.read_transcript((n_coeffs - 2) * EF::DIMENSION)?;
                let rest_bare: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                let h0 = claimed_sum - alpha * rest_bare.iter().copied().sum::<EF>();

                let mut bare = Vec::with_capacity(n_coeffs - 1);
                bare.push(h0);
                bare.extend_from_slice(&rest_bare);

                let full_coeffs = expand_bare_to_full(&bare, alpha);
                self.absorb_and_record(&flatten_scalars_to_base(&full_coeffs));
                Ok(full_coeffs)
            }
        }
    }
}

pub struct VerifierStateSha2<EF: ExtensionField<PF<EF>>> {
    challenger: ChallengerSha2<PF<EF>>,
    transcript: Vec<PF<EF>>,
    transcript_offset: usize,
    commitments: Vec<Sha256Digest>,
    commitment_index: usize,
    merkle_openings: Vec<MerkleOpening<PF<EF>, Sha256Digest>>,
    merkle_opening_index: usize,
}

impl<EF: ExtensionField<PF<EF>>> VerifierStateSha2<EF>
where
    PF<EF>: PrimeField32,
{
    pub fn new(proof: Proof<PF<EF>, Sha256Digest>) -> Result<Self, ProofError> {
        let mut merkle_openings = Vec::new();
        for paths in proof.merkle_paths {
            let restored = Self::restore_merkle_paths(paths).ok_or(ProofError::InvalidProof)?;
            merkle_openings.extend(restored);
        }

        Ok(Self {
            challenger: ChallengerSha2::new(),
            transcript: proof.transcript,
            transcript_offset: 0,
            commitments: proof.commitments,
            commitment_index: 0,
            merkle_openings,
            merkle_opening_index: 0,
        })
    }

    fn read_transcript(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        if self.transcript_offset + n > self.transcript.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.transcript_offset..self.transcript_offset + n].to_vec();
        self.transcript_offset += n;
        Ok(scalars)
    }

    fn restore_merkle_paths(
        paths: PrunedMerklePaths<PF<EF>, Sha256Digest>,
    ) -> Option<Vec<MerkleOpening<PF<EF>, Sha256Digest>>> {
        let hash_fn = |data: &[PF<EF>]| {
            let mut hasher = Sha256::new();
            for value in data {
                hasher.update(value.as_canonical_u32().to_le_bytes());
            }
            let digest = hasher.finalize();
            digest[..16].try_into().unwrap()
        };
        let combine_fn = |left: &Sha256Digest, right: &Sha256Digest| {
            let mut hasher = Sha256::new();
            hasher.update(left);
            hasher.update(right);
            let digest = hasher.finalize();
            digest[..16].try_into().unwrap()
        };
        let restored = paths.restore(&hash_fn, &combine_fn)?;
        Some(
            restored
                .0
                .into_iter()
                .map(|path| MerkleOpening {
                    leaf_data: path.leaf_data,
                    path: path.sibling_hashes,
                })
                .collect(),
        )
    }
}

impl<EF: ExtensionField<PF<EF>>> ChallengeSampler<EF> for VerifierStateSha2<EF>
where
    PF<EF>: PrimeField32,
{
    fn sample_vec(&mut self, len: usize) -> Vec<EF> {
        let sampled_fe = self
            .challenger
            .sample_many((len * EF::DIMENSION).div_ceil(RATE))
            .into_iter()
            .flatten()
            .take(len * EF::DIMENSION)
            .collect::<Vec<PF<EF>>>();
        pack_scalars_to_extension(&sampled_fe)
    }

    fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        self.challenger.sample_in_range(bits, n_samples)
    }
}

impl<EF: ExtensionField<PF<EF>>> FSVerifier<EF> for VerifierStateSha2<EF>
where
    PF<EF>: PrimeField32,
{
    type Digest = Sha256Digest;

    fn state(&self) -> String {
        format!(
            "sha2 verifier (offset: {}, commitment_idx: {}, merkle_idx: {})",
            self.transcript_offset, self.commitment_index, self.merkle_opening_index,
        )
    }

    fn observe_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_scalars(scalars);
    }

    fn next_base_scalars_vec(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        let scalars = self.read_transcript(n)?;
        self.challenger.observe_scalars(&scalars);
        Ok(scalars)
    }

    fn next_commitment(&mut self) -> Result<Self::Digest, ProofError> {
        if self.commitment_index >= self.commitments.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let commitment = self.commitments[self.commitment_index];
        self.commitment_index += 1;
        self.challenger.observe_bytes(&commitment);
        Ok(commitment)
    }

    fn next_merkle_opening(&mut self) -> Result<MerkleOpening<PF<EF>, Self::Digest>, ProofError> {
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
        let witness = self.read_transcript(1)?[0];
        self.challenger.observe_scalars(&[witness]);
        let mut challenger = self.challenger.clone();
        if challenger.sample_in_range(bits, 1)[0] != 0 {
            return Err(ProofError::InvalidGrindingWitness);
        }
        Ok(())
    }

    fn next_sumcheck_polynomial(
        &mut self,
        n_coeffs: usize,
        claimed_sum: EF,
        eq_alpha: Option<EF>,
    ) -> ProofResult<Vec<EF>> {
        match eq_alpha {
            None => {
                let rest_scalars = self.read_transcript((n_coeffs - 1) * EF::DIMENSION)?;
                let rest_coeffs: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                let c0 = (claimed_sum - rest_coeffs.iter().copied().sum::<EF>()).halve();

                let mut full_coeffs = Vec::with_capacity(n_coeffs);
                full_coeffs.push(c0);
                full_coeffs.extend_from_slice(&rest_coeffs);

                let mut all_scalars = flatten_scalars_to_base(&[c0]);
                all_scalars.extend_from_slice(&rest_scalars);
                self.challenger.observe_scalars(&all_scalars);
                Ok(full_coeffs)
            }
            Some(alpha) => {
                let rest_scalars = self.read_transcript((n_coeffs - 2) * EF::DIMENSION)?;
                let rest_bare: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                let h0 = claimed_sum - alpha * rest_bare.iter().copied().sum::<EF>();

                let mut bare = Vec::with_capacity(n_coeffs - 1);
                bare.push(h0);
                bare.extend_from_slice(&rest_bare);

                let full_coeffs = expand_bare_to_full(&bare, alpha);
                self.challenger.observe_scalars(&flatten_scalars_to_base(&full_coeffs));
                Ok(full_coeffs)
            }
        }
    }
}
