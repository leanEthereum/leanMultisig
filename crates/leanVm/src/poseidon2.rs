use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBear, Poseidon2KoalaBear};
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::{Poseidon2Air, RoundConstants, generate_trace_rows};
use rand::{SeedableRng, rngs::StdRng};

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

#[must_use]
pub fn build_poseidon16() -> Poseidon16 {
    Poseidon16::new_from_rng_128(&mut StdRng::seed_from_u64(0))
}

#[must_use]
pub fn build_poseidon24() -> Poseidon24 {
    Poseidon24::new_from_rng_128(&mut StdRng::seed_from_u64(0))
}

#[must_use]
pub fn build_poseidon_16_air() -> Poseidon16Air {
    Poseidon16Air::new(build_poseidon16_constants())
}

#[must_use]
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

#[must_use]
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

#[must_use]
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
