use std::sync::OnceLock;

use p3_koala_bear::KOALABEAR_RC16_EXTERNAL_FINAL;
use p3_koala_bear::KOALABEAR_RC16_EXTERNAL_INITIAL;
use p3_koala_bear::KOALABEAR_RC16_INTERNAL;
use p3_koala_bear::KoalaBear;
use p3_koala_bear::Poseidon2KoalaBear;
use p3_poseidon2::ExternalLayerConstants;
use p3_symmetric::Permutation;

pub type Poseidon16 = Poseidon2KoalaBear<16>;
pub type Poseidon24 = Poseidon2KoalaBear<24>;

pub const QUARTER_FULL_ROUNDS_16: usize = 2;
pub const HALF_FULL_ROUNDS_16: usize = 4;
pub const PARTIAL_ROUNDS_16: usize = 20;

static POSEIDON_16_INSTANCE: OnceLock<Poseidon16> = OnceLock::new();
static POSEIDON_16_OF_ZERO: OnceLock<[KoalaBear; 16]> = OnceLock::new();

#[inline(always)]
pub(crate) fn get_poseidon16() -> &'static Poseidon16 {
    POSEIDON_16_INSTANCE.get_or_init(|| {
        let external_constants = ExternalLayerConstants::new(
            KOALABEAR_RC16_EXTERNAL_INITIAL.to_vec(),
            KOALABEAR_RC16_EXTERNAL_FINAL.to_vec(),
        );
        Poseidon16::new(external_constants, KOALABEAR_RC16_INTERNAL.to_vec())
    })
}

#[inline(always)]
pub fn get_poseidon_16_of_zero() -> &'static [KoalaBear; 16] {
    POSEIDON_16_OF_ZERO.get_or_init(|| poseidon16_permute([KoalaBear::default(); 16]))
}

#[inline(always)]
pub fn poseidon16_permute(input: [KoalaBear; 16]) -> [KoalaBear; 16] {
    get_poseidon16().permute(input)
}

#[inline(always)]
pub fn poseidon16_permute_mut(input: &mut [KoalaBear; 16]) {
    get_poseidon16().permute_mut(input);
}
