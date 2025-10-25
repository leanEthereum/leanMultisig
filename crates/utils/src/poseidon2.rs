use std::sync::OnceLock;

use p3_koala_bear::KOALABEAR_RC16_EXTERNAL_FINAL;
use p3_koala_bear::KOALABEAR_RC16_EXTERNAL_INITIAL;
use p3_koala_bear::KOALABEAR_RC16_INTERNAL;
use p3_koala_bear::KOALABEAR_RC24_EXTERNAL_FINAL;
use p3_koala_bear::KOALABEAR_RC24_EXTERNAL_INITIAL;
use p3_koala_bear::KOALABEAR_RC24_INTERNAL;
use p3_koala_bear::KoalaBear;
use p3_koala_bear::Poseidon2KoalaBear;
use p3_poseidon2::ExternalLayerConstants;
use p3_poseidon2_air::p16::RoundConstants16;
use p3_poseidon2_air::p24::RoundConstants24;
use p3_symmetric::Permutation;

pub type Poseidon16 = Poseidon2KoalaBear<16>;
pub type Poseidon24 = Poseidon2KoalaBear<24>;

pub const QUARTER_FULL_ROUNDS_16: usize = 2;
pub const HALF_FULL_ROUNDS_16: usize = 4;
pub const PARTIAL_ROUNDS_16: usize = 20;

pub const QUARTER_FULL_ROUNDS_24: usize = 2;
pub const HALF_FULL_ROUNDS_24: usize = 4;
pub const PARTIAL_ROUNDS_24: usize = 23;

pub type MyRoundConstants16<F> = RoundConstants16<F, 16, HALF_FULL_ROUNDS_16, PARTIAL_ROUNDS_16>;
pub type MyRoundConstants24<F> = RoundConstants24<F, 24, HALF_FULL_ROUNDS_24, PARTIAL_ROUNDS_24>;

static POSEIDON16_INSTANCE: OnceLock<Poseidon16> = OnceLock::new();

#[inline(always)]
pub(crate) fn get_poseidon16() -> &'static Poseidon16 {
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

#[inline(always)]
pub fn poseidon16_permute(input: [KoalaBear; 16]) -> [KoalaBear; 16] {
    get_poseidon16().permute(input)
}

#[inline(always)]
pub fn poseidon16_permute_mut(input: &mut [KoalaBear; 16]) {
    get_poseidon16().permute_mut(input);
}

#[inline(always)]
pub fn poseidon24_permute(input: [KoalaBear; 24]) -> [KoalaBear; 24] {
    get_poseidon24().permute(input)
}

#[inline(always)]
pub fn poseidon24_permute_mut(input: &mut [KoalaBear; 24]) {
    get_poseidon24().permute_mut(input);
}

static POSEIDON24_INSTANCE: OnceLock<Poseidon24> = OnceLock::new();

#[inline(always)]
pub(crate) fn get_poseidon24() -> &'static Poseidon24 {
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

pub fn build_poseidon16_constants() -> MyRoundConstants16<KoalaBear> {
    RoundConstants16 {
        beginning_full_round_constants: KOALABEAR_RC16_EXTERNAL_INITIAL,
        partial_round_constants: KOALABEAR_RC16_INTERNAL,
        ending_full_round_constants: KOALABEAR_RC16_EXTERNAL_FINAL,
    }
}

pub fn build_poseidon24_constants() -> MyRoundConstants24<KoalaBear> {
    RoundConstants24 {
        beginning_full_round_constants: KOALABEAR_RC24_EXTERNAL_INITIAL,
        partial_round_constants: KOALABEAR_RC24_INTERNAL,
        ending_full_round_constants: KOALABEAR_RC24_EXTERNAL_FINAL,
    }
}

