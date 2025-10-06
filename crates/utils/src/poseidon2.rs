use std::sync::OnceLock;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::GenericPoseidon2LinearLayersKoalaBear;
use p3_koala_bear::KOALABEAR_RC16_EXTERNAL_FINAL;
use p3_koala_bear::KOALABEAR_RC16_EXTERNAL_INITIAL;
use p3_koala_bear::KOALABEAR_RC16_INTERNAL;
use p3_koala_bear::KOALABEAR_RC24_EXTERNAL_FINAL;
use p3_koala_bear::KOALABEAR_RC24_EXTERNAL_INITIAL;
use p3_koala_bear::KOALABEAR_RC24_INTERNAL;
use p3_koala_bear::KoalaBear;
use p3_koala_bear::Poseidon2KoalaBear;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2::ExternalLayerConstants;
use p3_poseidon2_air::p16::Poseidon2Air16;
use p3_poseidon2_air::p16::RoundConstants16;
use p3_poseidon2_air::p16::generate_trace_rows_16;
use p3_poseidon2_air::p24::Poseidon2Air24;
use p3_poseidon2_air::p24::RoundConstants24;
use p3_poseidon2_air::p24::generate_trace_rows_24;

pub type Poseidon16 = Poseidon2KoalaBear<16>;
pub type Poseidon24 = Poseidon2KoalaBear<24>;

pub const QUARTER_FULL_ROUNDS_16: usize = 2;
pub const HALF_FULL_ROUNDS_16: usize = 4;
pub const PARTIAL_ROUNDS_16: usize = 20;

pub const QUARTER_FULL_ROUNDS_24: usize = 2;
pub const HALF_FULL_ROUNDS_24: usize = 4;
pub const PARTIAL_ROUNDS_24: usize = 23;

pub const SBOX_DEGREE: u64 = 3;
pub const SBOX_REGISTERS: usize = 0;

pub type MyLinearLayers = GenericPoseidon2LinearLayersKoalaBear;

pub type Poseidon16Air<F> = Poseidon2Air16<
    F,
    MyLinearLayers,
    16,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    QUARTER_FULL_ROUNDS_16,
    HALF_FULL_ROUNDS_16,
    PARTIAL_ROUNDS_16,
>;

pub type Poseidon24Air<F> = Poseidon2Air24<
    F,
    MyLinearLayers,
    24,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    QUARTER_FULL_ROUNDS_24,
    HALF_FULL_ROUNDS_24,
    PARTIAL_ROUNDS_24,
>;

static POSEIDON16_INSTANCE: OnceLock<Poseidon16> = OnceLock::new();

pub fn get_poseidon16() -> &'static Poseidon16 {
    POSEIDON16_INSTANCE.get_or_init(|| {
        let round_constants = build_poseidon16_constants();
        let external_constants = ExternalLayerConstants::new(
            round_constants.beginning_full_round_constants.to_vec(),
            round_constants.ending_full_round_constants.to_vec(),
        );
        Poseidon16::new(
            external_constants,
            round_constants.partial_round_constants.to_vec(),
        )
    })
}

static POSEIDON24_INSTANCE: OnceLock<Poseidon24> = OnceLock::new();

pub fn get_poseidon24() -> &'static Poseidon24 {
    POSEIDON24_INSTANCE.get_or_init(|| {
        let round_constants = build_poseidon24_constants();
        let external_constants = ExternalLayerConstants::new(
            round_constants.beginning_full_round_constants.to_vec(),
            round_constants.ending_full_round_constants.to_vec(),
        );
        Poseidon24::new(
            external_constants,
            round_constants.partial_round_constants.to_vec(),
        )
    })
}

pub fn build_poseidon_16_air() -> Poseidon16Air<KoalaBear> {
    Poseidon16Air::new(build_poseidon16_constants())
}

pub fn build_poseidon_24_air() -> Poseidon24Air<KoalaBear> {
    Poseidon24Air::new(build_poseidon24_constants())
}

pub fn build_poseidon_16_air_packed() -> Poseidon16Air<PFPacking<KoalaBear>> {
    Poseidon16Air::new(build_poseidon16_constants_packed())
}

pub fn build_poseidon_24_air_packed() -> Poseidon24Air<PFPacking<KoalaBear>> {
    Poseidon24Air::new(build_poseidon24_constants_packed())
}

fn build_poseidon16_constants()
-> RoundConstants16<KoalaBear, 16, HALF_FULL_ROUNDS_16, PARTIAL_ROUNDS_16> {
    RoundConstants16 {
        beginning_full_round_constants: KOALABEAR_RC16_EXTERNAL_INITIAL,
        partial_round_constants: KOALABEAR_RC16_INTERNAL,
        ending_full_round_constants: KOALABEAR_RC16_EXTERNAL_FINAL,
    }
}

fn build_poseidon24_constants()
-> RoundConstants24<KoalaBear, 24, HALF_FULL_ROUNDS_24, PARTIAL_ROUNDS_24> {
    RoundConstants24 {
        beginning_full_round_constants: KOALABEAR_RC24_EXTERNAL_INITIAL,
        partial_round_constants: KOALABEAR_RC24_INTERNAL,
        ending_full_round_constants: KOALABEAR_RC24_EXTERNAL_FINAL,
    }
}

fn build_poseidon16_constants_packed()
-> RoundConstants16<PFPacking<KoalaBear>, 16, HALF_FULL_ROUNDS_16, PARTIAL_ROUNDS_16> {
    let normal_constants = build_poseidon16_constants();
    RoundConstants16 {
        beginning_full_round_constants: normal_constants
            .beginning_full_round_constants
            .map(|arr| arr.map(Into::into)),
        partial_round_constants: normal_constants.partial_round_constants.map(Into::into),
        ending_full_round_constants: normal_constants
            .ending_full_round_constants
            .map(|arr| arr.map(Into::into)),
    }
}

fn build_poseidon24_constants_packed()
-> RoundConstants24<PFPacking<KoalaBear>, 24, HALF_FULL_ROUNDS_24, PARTIAL_ROUNDS_24> {
    let normal_constants = build_poseidon24_constants();
    RoundConstants24 {
        beginning_full_round_constants: normal_constants
            .beginning_full_round_constants
            .map(|arr| arr.map(Into::into)),
        partial_round_constants: normal_constants.partial_round_constants.map(Into::into),
        ending_full_round_constants: normal_constants
            .ending_full_round_constants
            .map(|arr| arr.map(Into::into)),
    }
}

pub fn generate_trace_poseidon_16(
    inputs: &[[KoalaBear; 16]],
    compress: &[bool],
    index_res: &[usize],
) -> RowMajorMatrix<KoalaBear> {
    generate_trace_rows_16::<
        KoalaBear,
        MyLinearLayers,
        16,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        QUARTER_FULL_ROUNDS_16,
        HALF_FULL_ROUNDS_16,
        PARTIAL_ROUNDS_16,
    >(
        inputs,
        compress,
        index_res,
        &build_poseidon16_constants(),
        0,
    )
}

pub fn generate_trace_poseidon_24(inputs: &[[KoalaBear; 24]]) -> RowMajorMatrix<KoalaBear> {
    generate_trace_rows_24::<
        KoalaBear,
        MyLinearLayers,
        24,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        QUARTER_FULL_ROUNDS_24,
        HALF_FULL_ROUNDS_24,
        PARTIAL_ROUNDS_24,
    >(inputs, &build_poseidon24_constants(), 0)
}
