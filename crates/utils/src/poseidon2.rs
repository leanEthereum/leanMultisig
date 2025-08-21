use p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear;
use p3_koala_bear::KoalaBear;
use p3_koala_bear::Poseidon2KoalaBear;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2::ExternalLayerConstants;
use p3_poseidon2_air::Poseidon2Air;
use p3_poseidon2_air::RoundConstants;
use p3_poseidon2_air::generate_trace_rows;
use rand::SeedableRng;
use rand::rngs::StdRng;

pub type Poseidon16 = Poseidon2KoalaBear<16>;
pub type Poseidon24 = Poseidon2KoalaBear<24>;

pub const HALF_FULL_ROUNDS_16: usize = 4;
pub const PARTIAL_ROUNDS_16: usize = 20;

pub const HALF_FULL_ROUNDS_24: usize = 4;
pub const PARTIAL_ROUNDS_24: usize = 23;

pub const SBOX_DEGREE: u64 = 3;
pub const SBOX_REGISTERS: usize = 0;

pub type MyLinearLayers = GenericPoseidon2LinearLayersKoalaBear;

pub type Poseidon16Air = Poseidon2Air<
    KoalaBear,
    MyLinearLayers,
    16,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS_16,
    PARTIAL_ROUNDS_16,
>;

pub type Poseidon24Air = Poseidon2Air<
    KoalaBear,
    MyLinearLayers,
    24,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS_24,
    PARTIAL_ROUNDS_24,
>;

pub fn build_poseidon16() -> Poseidon16 {
    let round_constants = build_poseidon16_constants();
    let external_constants = ExternalLayerConstants::new(
        round_constants.beginning_full_round_constants.to_vec(),
        round_constants.ending_full_round_constants.to_vec(),
    );
    Poseidon16::new(
        external_constants,
        round_constants.partial_round_constants.to_vec(),
    )
}

pub fn build_poseidon24() -> Poseidon24 {
    let round_constants = build_poseidon24_constants();
    let external_constants = ExternalLayerConstants::new(
        round_constants.beginning_full_round_constants.to_vec(),
        round_constants.ending_full_round_constants.to_vec(),
    );
    Poseidon24::new(
        external_constants,
        round_constants.partial_round_constants.to_vec(),
    )
}

pub fn build_poseidon_16_air() -> Poseidon16Air {
    Poseidon16Air::new(build_poseidon16_constants())
}

pub fn build_poseidon_24_air() -> Poseidon24Air {
    Poseidon24Air::new(build_poseidon24_constants())
}

fn build_poseidon16_constants()
-> RoundConstants<KoalaBear, 16, HALF_FULL_ROUNDS_16, PARTIAL_ROUNDS_16> {
    RoundConstants::<KoalaBear, 16, HALF_FULL_ROUNDS_16, PARTIAL_ROUNDS_16>::from_rng(
        &mut StdRng::seed_from_u64(0),
    )
}

fn build_poseidon24_constants()
-> RoundConstants<KoalaBear, 24, HALF_FULL_ROUNDS_24, PARTIAL_ROUNDS_24> {
    RoundConstants::<KoalaBear, 24, HALF_FULL_ROUNDS_24, PARTIAL_ROUNDS_24>::from_rng(
        &mut StdRng::seed_from_u64(0),
    )
}

pub fn generate_trace_poseidon_16(inputs: Vec<[KoalaBear; 16]>) -> RowMajorMatrix<KoalaBear> {
    generate_trace_rows::<
        KoalaBear,
        MyLinearLayers,
        16,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS_16,
        PARTIAL_ROUNDS_16,
    >(inputs, &build_poseidon16_constants(), 0)
}

pub fn generate_trace_poseidon_24(inputs: Vec<[KoalaBear; 24]>) -> RowMajorMatrix<KoalaBear> {
    generate_trace_rows::<
        KoalaBear,
        MyLinearLayers,
        24,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS_24,
        PARTIAL_ROUNDS_24,
    >(inputs, &build_poseidon24_constants(), 0)
}
