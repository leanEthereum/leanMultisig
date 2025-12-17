use leansig::{
    inc_encoding::target_sum::TargetSumEncoding,
    signature::generalized_xmss::{GeneralizedXMSSPublicKey, GeneralizedXMSSSignature, GeneralizedXMSSSignatureScheme},
    symmetric::{
        message_hash::top_level_poseidon::TopLevelPoseidonMessageHash, prf::shake_to_field::ShakePRFtoF,
        tweak_hash::poseidon::PoseidonTweakHash,
    },
};

pub mod prod_config {
    use super::*;

    pub(crate) const IS_PROD_CONFIG: bool = true;

    pub(crate) const LOG_LIFETIME: usize = 32;

    pub(crate) const DIMENSION: usize = 64;
    pub(crate) const BASE: usize = 8;
    pub(crate) const FINAL_LAYER: usize = 77;
    pub(crate) const TARGET_SUM: usize = 375;

    pub(crate) const PARAMETER_LEN: usize = 5;
    pub(crate) const TWEAK_LEN_FE: usize = 2;
    pub(crate) const MSG_LEN_FE: usize = 9;
    pub(crate) const RAND_LEN_FE: usize = 7;
    pub(crate) const HASH_LEN_FE: usize = 8;

    pub(crate) const CAPACITY: usize = 9;

    const POS_OUTPUT_LEN_PER_INV_FE: usize = 15;
    const POS_INVOCATIONS: usize = 1;
    const POS_OUTPUT_LEN_FE: usize = POS_OUTPUT_LEN_PER_INV_FE * POS_INVOCATIONS;

    pub(crate) type MH = TopLevelPoseidonMessageHash<
        POS_OUTPUT_LEN_PER_INV_FE,
        POS_INVOCATIONS,
        POS_OUTPUT_LEN_FE,
        DIMENSION,
        BASE,
        FINAL_LAYER,
        TWEAK_LEN_FE,
        MSG_LEN_FE,
        PARAMETER_LEN,
        RAND_LEN_FE,
    >;

    type TH = PoseidonTweakHash<PARAMETER_LEN, HASH_LEN_FE, TWEAK_LEN_FE, CAPACITY, DIMENSION>;
    type PRF = ShakePRFtoF<HASH_LEN_FE, RAND_LEN_FE>;
    type IE = TargetSumEncoding<MH, TARGET_SUM>;

    pub type LeanSigScheme = GeneralizedXMSSSignatureScheme<PRF, IE, TH, LOG_LIFETIME>;
    pub type LeanSigPubKey = GeneralizedXMSSPublicKey<TH>;
    pub type LeanSigSignature = GeneralizedXMSSSignature<IE, TH>;
}

pub mod test_config {
    use super::*;

    pub(crate) const IS_PROD_CONFIG: bool = false;

    pub(crate) const LOG_LIFETIME: usize = 8;

    pub(crate) const DIMENSION: usize = 4;
    pub(crate) const BASE: usize = 4;
    pub(crate) const FINAL_LAYER: usize = 6;
    pub(crate) const TARGET_SUM: usize = 6;

    pub(crate) const PARAMETER_LEN: usize = 5;
    pub(crate) const TWEAK_LEN_FE: usize = 2;
    const MSG_LEN_FE: usize = 9;
    pub(crate) const RAND_LEN_FE: usize = 7;
    pub(crate) const HASH_LEN_FE: usize = 8;

    pub(crate) const CAPACITY: usize = 9;

    const POS_OUTPUT_LEN_PER_INV_FE: usize = 15;
    const POS_INVOCATIONS: usize = 1;
    const POS_OUTPUT_LEN_FE: usize = POS_OUTPUT_LEN_PER_INV_FE * POS_INVOCATIONS;

    pub(crate) type MH = TopLevelPoseidonMessageHash<
        POS_OUTPUT_LEN_PER_INV_FE,
        POS_INVOCATIONS,
        POS_OUTPUT_LEN_FE,
        DIMENSION,
        BASE,
        FINAL_LAYER,
        TWEAK_LEN_FE,
        MSG_LEN_FE,
        PARAMETER_LEN,
        RAND_LEN_FE,
    >;

    type TH = PoseidonTweakHash<PARAMETER_LEN, HASH_LEN_FE, TWEAK_LEN_FE, CAPACITY, DIMENSION>;
    type PRF = ShakePRFtoF<HASH_LEN_FE, RAND_LEN_FE>;
    type IE = TargetSumEncoding<MH, TARGET_SUM>;

    pub type LeanSigScheme = GeneralizedXMSSSignatureScheme<PRF, IE, TH, LOG_LIFETIME>;
    pub type LeanSigPubKey = GeneralizedXMSSPublicKey<TH>;
    pub type LeanSigSignature = GeneralizedXMSSSignature<IE, TH>;
}
