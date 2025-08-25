use p3_challenger::DuplexChallenger;
use p3_field::{
    ExtensionField, Field, PackedFieldExtension, PackedValue, PrimeCharacteristicRing, PrimeField64,
};
use p3_koala_bear::KoalaBear;
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation,
};
use rayon::prelude::*;
use whir_p3::{
    fiat_shamir::{prover::ProverState, verifier::VerifierState},
    whir::config::WhirConfigBuilder,
};

use crate::{Poseidon16, Poseidon24, build_poseidon16, build_poseidon24};

pub type PF<F> = <F as PrimeCharacteristicRing>::PrimeSubfield;
pub type PFPacking<F> = <PF<F> as Field>::Packing;
pub type EFPacking<EF> = <EF as ExtensionField<PF<EF>>>::ExtensionPacking;

pub type FSProver<EF, Challenger> = ProverState<PF<EF>, EF, Challenger>;
pub type FSVerifier<EF, Challenger> = VerifierState<PF<EF>, EF, Challenger>;

pub type MyMerkleHash = PaddingFreeSponge<Poseidon24, 24, 16, 8>; // leaf hashing
pub type MyMerkleCompress = TruncatedPermutation<Poseidon16, 2, 8, 16>; // 2-to-1 compression
pub type MyChallenger = DuplexChallenger<KoalaBear, Poseidon16, 16, 8>;
pub type MyWhirConfigBuilder<F, EF> =
    WhirConfigBuilder<F, EF, MyMerkleHash, MyMerkleCompress, MY_DIGEST_ELEMS>;
pub const MY_DIGEST_ELEMS: usize = 8;

pub trait MerkleHasher<EF: Field>:
    CryptographicHasher<PFPacking<EF>, [PFPacking<EF>; MY_DIGEST_ELEMS]>
    + CryptographicHasher<PF<EF>, [PF<EF>; MY_DIGEST_ELEMS]>
    + Sync
{
}

pub trait MerkleCompress<EF: Field>:
    PseudoCompressionFunction<[PFPacking<EF>; MY_DIGEST_ELEMS], 2>
    + PseudoCompressionFunction<[PF<EF>; MY_DIGEST_ELEMS], 2>
    + Sync
{
}

impl<
    EF: Field,
    MH: CryptographicHasher<PFPacking<EF>, [PFPacking<EF>; MY_DIGEST_ELEMS]>
        + CryptographicHasher<PF<EF>, [PF<EF>; MY_DIGEST_ELEMS]>
        + Sync,
> MerkleHasher<EF> for MH
{
}

impl<
    EF: Field,
    MC: PseudoCompressionFunction<[PFPacking<EF>; MY_DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[PF<EF>; MY_DIGEST_ELEMS], 2>
        + Sync,
> MerkleCompress<EF> for MC
{
}

pub fn pack_extension<EF: ExtensionField<PF<EF>>>(slice: &[EF]) -> Vec<EFPacking<EF>> {
    slice
        .par_chunks_exact(packing_width::<EF>())
        .map(EFPacking::<EF>::from_ext_slice)
        .collect()
}

pub fn unpack_extension<EF: ExtensionField<PF<EF>>>(vec: &[EFPacking<EF>]) -> Vec<EF> {
    EFPacking::<EF>::to_ext_iter(vec.iter().copied()).collect()
}

#[must_use]
pub const fn packing_log_width<EF: Field>() -> usize {
    packing_width::<EF>().ilog2() as usize
}

#[must_use]
pub const fn packing_width<EF: Field>() -> usize {
    PFPacking::<EF>::WIDTH
}

#[must_use]
pub fn build_challenger() -> MyChallenger {
    MyChallenger::new(build_poseidon16())
}

#[must_use]
pub fn build_merkle_hash() -> MyMerkleHash {
    MyMerkleHash::new(build_poseidon24())
}

#[must_use]
pub fn build_merkle_compress() -> MyMerkleCompress {
    MyMerkleCompress::new(build_poseidon16())
}

#[must_use]
pub fn build_prover_state<EF: ExtensionField<KoalaBear>>()
-> ProverState<KoalaBear, EF, MyChallenger> {
    ProverState::new(build_challenger())
}

#[must_use]
pub fn build_verifier_state<EF: ExtensionField<KoalaBear>>(
    prover_state: &ProverState<KoalaBear, EF, MyChallenger>,
) -> VerifierState<KoalaBear, EF, MyChallenger> {
    VerifierState::new(prover_state.proof_data().to_vec(), build_challenger())
}

pub trait ToUsize {
    fn to_usize(self) -> usize;
}

impl<F: PrimeField64> ToUsize for F {
    fn to_usize(self) -> usize {
        self.as_canonical_u64() as usize
    }
}
