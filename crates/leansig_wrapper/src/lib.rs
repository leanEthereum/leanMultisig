use backend::KoalaBear;

pub const V: usize = 46;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const TARGET_SUM: usize = 200;
pub const LOG_LIFETIME: usize = 32;
pub const RANDOMNESS_LEN_FE: usize = 7;
pub const MESSAGE_LEN_FE: usize = 9;
pub const PUBLIC_PARAM_LEN_FE: usize = 5;
pub const TWEAK_LEN: usize = 2;
pub const POSEIDON24_CAPACITY: usize = 9;
pub const POSEIDON24_RATE: usize = 15;
pub const DIGEST_SIZE_FE: usize = 8;

pub const SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + (V + LOG_LIFETIME) * DIGEST_SIZE_FE;

pub(crate) type F = KoalaBear;

pub const WOTS_PUBKET_SPONGE_DOMAIN_SEP: [F; POSEIDON24_CAPACITY] = F::new_array([
    2060061975, 916902315, 229801915, 83751504, 2093549181, 1743125625, 721042244, 1252069948, 1192880636,
]);
