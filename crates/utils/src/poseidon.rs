use backend::*;
use std::sync::OnceLock;

pub type Poseidon16 = Poseidon1KoalaBear16;

pub const HALF_FULL_ROUNDS_16: usize = POSEIDON1_HALF_FULL_ROUNDS;
pub const PARTIAL_ROUNDS_16: usize = POSEIDON1_PARTIAL_ROUNDS;

static POSEIDON_16_INSTANCE: OnceLock<Poseidon16> = OnceLock::new();
static POSEIDON_16_OF_ZERO: OnceLock<[KoalaBear; 8]> = OnceLock::new();

#[inline(always)]
pub fn get_poseidon16() -> &'static Poseidon16 {
    POSEIDON_16_INSTANCE.get_or_init(default_koalabear_poseidon1_16)
}

#[inline(always)]
pub fn get_poseidon_16_of_zero() -> &'static [KoalaBear; 8] {
    POSEIDON_16_OF_ZERO.get_or_init(|| poseidon16_compress([KoalaBear::default(); 16]))
}

#[inline(always)]
pub fn poseidon16_compress(input: [KoalaBear; 16]) -> [KoalaBear; 8] {
    get_poseidon16().compress(input)[0..8].try_into().unwrap()
}

pub fn poseidon16_compress_pair(left: [KoalaBear; 8], right: [KoalaBear; 8]) -> [KoalaBear; 8] {
    let mut input = [KoalaBear::default(); 16];
    input[..8].copy_from_slice(&left);
    input[8..].copy_from_slice(&right);
    poseidon16_compress(input)
}

/// Requires the length of the slice to be constant (not malleable), otherwise IV should be added
pub fn poseidon_compress_slice(data: &[KoalaBear]) -> [KoalaBear; 8] {
    assert!(!data.is_empty());
    let len = data.len();
    if len <= 16 {
        let mut padded = [KoalaBear::default(); 16];
        padded[..len].copy_from_slice(data);
        return poseidon16_compress(padded);
    }
    let mut hash = poseidon16_compress(data[0..16].try_into().unwrap());
    for chunk in data[16..].chunks(8) {
        let mut block = [KoalaBear::default(); 16];
        block[..8].copy_from_slice(&hash);
        block[8..8 + chunk.len()].copy_from_slice(chunk);
        hash = poseidon16_compress(block);
    }
    hash
}
