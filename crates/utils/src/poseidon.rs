use backend::*;
use std::sync::OnceLock;

pub type Poseidon8 = Poseidon1Goldilocks8;

pub const HALF_FULL_ROUNDS_8: usize = POSEIDON1_HALF_FULL_ROUNDS;
pub const PARTIAL_ROUNDS_8: usize = POSEIDON1_PARTIAL_ROUNDS;

static POSEIDON_8_INSTANCE: OnceLock<Poseidon8> = OnceLock::new();
static POSEIDON_8_OF_ZERO: OnceLock<[Goldilocks; 4]> = OnceLock::new();

#[inline(always)]
pub fn get_poseidon8() -> &'static Poseidon8 {
    POSEIDON_8_INSTANCE.get_or_init(default_goldilocks_poseidon1_8)
}

#[inline(always)]
pub fn get_poseidon_8_of_zero() -> &'static [Goldilocks; 4] {
    POSEIDON_8_OF_ZERO.get_or_init(|| poseidon8_compress([Goldilocks::default(); 8]))
}

#[inline(always)]
pub fn poseidon8_compress(input: [Goldilocks; 8]) -> [Goldilocks; 4] {
    get_poseidon8().compress(input)[0..4].try_into().unwrap()
}

pub fn poseidon8_compress_pair(
    left: &[Goldilocks; 4],
    right: &[Goldilocks; 4],
) -> [Goldilocks; 4] {
    let mut input = [Goldilocks::default(); 8];
    input[..4].copy_from_slice(left);
    input[4..].copy_from_slice(right);
    poseidon8_compress(input)
}

/// If `use_iv` is false, the length of the slice must be constant (not malleable).
pub fn poseidon_compress_slice(data: &[Goldilocks], use_iv: bool) -> [Goldilocks; 4] {
    assert!(!data.is_empty());
    if use_iv {
        let mut hash = [Goldilocks::default(); 4];
        for chunk in data.chunks(4) {
            let mut block = [Goldilocks::default(); 8];
            block[..4].copy_from_slice(&hash);
            block[4..4 + chunk.len()].copy_from_slice(chunk);
            hash = poseidon8_compress(block);
        }
        hash
    } else {
        let len = data.len();
        if len <= 8 {
            let mut padded = [Goldilocks::default(); 8];
            padded[..len].copy_from_slice(data);
            return poseidon8_compress(padded);
        }
        let mut hash = poseidon8_compress(data[0..8].try_into().unwrap());
        for chunk in data[8..].chunks(4) {
            let mut block = [Goldilocks::default(); 8];
            block[..4].copy_from_slice(&hash);
            block[4..4 + chunk.len()].copy_from_slice(chunk);
            hash = poseidon8_compress(block);
        }
        hash
    }
}
