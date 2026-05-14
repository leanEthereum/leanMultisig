use core::{
    borrow::{Borrow, BorrowMut},
    mem::size_of,
};

use super::{
    SHA256_BLOCK_LIMBS, SHA256_BLOCK_WORDS, SHA256_COMPRESS_ROUNDS, SHA256_SCHEDULE_EXTENSIONS, SHA256_STATE_WORDS,
    SHA256_U32_LIMBS, SHA256_WORD_BITS,
};

pub const SHA256_CHAIN_LEN: usize = 4 + SHA256_COMPRESS_ROUNDS;

pub const SHA256_COL_FLAG: usize = 0;
pub const SHA256_COL_STATE_PTR: usize = 1;
pub const SHA256_COL_BLOCK_PTR: usize = 2;
pub const SHA256_COL_OUT_PTR: usize = 3;
pub const SHA256_COL_BLOCK_LIMBS_START: usize = 4;
pub const SHA256_COL_AIR_START: usize = SHA256_COL_BLOCK_LIMBS_START + SHA256_BLOCK_LIMBS;
pub const SHA256_COL_STATE_LIMBS_START: usize = SHA256_COL_AIR_START;
pub const SHA256_COL_OUT_LIMBS_START: usize = NUM_SHA256_COMPRESS_COLS - SHA256_STATE_WORDS * SHA256_U32_LIMBS;

#[repr(C)]
#[derive(Debug)]
pub struct Sha256RoundCols<T> {
    pub sigma1_e: [T; SHA256_U32_LIMBS],
    pub ch: [T; SHA256_U32_LIMBS],
    pub tmp1: [T; SHA256_U32_LIMBS],
    pub t1: [T; SHA256_U32_LIMBS],
    pub sigma0_a: [T; SHA256_U32_LIMBS],
    pub maj: [T; SHA256_U32_LIMBS],
}

#[repr(C)]
#[derive(Debug)]
pub struct Sha256Cols<T> {
    pub h_in: [[T; SHA256_U32_LIMBS]; SHA256_STATE_WORDS],
    pub a_chain: [[T; SHA256_WORD_BITS]; SHA256_CHAIN_LEN],
    pub e_chain: [[T; SHA256_WORD_BITS]; SHA256_CHAIN_LEN],
    pub w: [[T; SHA256_WORD_BITS]; SHA256_COMPRESS_ROUNDS],
    pub sched_sigma0: [[T; SHA256_U32_LIMBS]; SHA256_SCHEDULE_EXTENSIONS],
    pub sched_sigma1: [[T; SHA256_U32_LIMBS]; SHA256_SCHEDULE_EXTENSIONS],
    pub sched_tmp: [[T; SHA256_U32_LIMBS]; SHA256_SCHEDULE_EXTENSIONS],
    pub rounds: [Sha256RoundCols<T>; SHA256_COMPRESS_ROUNDS],
    pub h_out: [[T; SHA256_U32_LIMBS]; SHA256_STATE_WORDS],
}

#[repr(C)]
#[derive(Debug)]
pub struct Sha256CompressCols<T> {
    pub flag: T,
    pub state_ptr: T,
    pub block_ptr: T,
    pub out_ptr: T,
    pub block_limbs: [[T; SHA256_U32_LIMBS]; SHA256_BLOCK_WORDS],
    pub sha: Sha256Cols<T>,
}

pub const NUM_SHA256_AIR_COLS: usize = size_of::<Sha256Cols<u8>>();
pub const NUM_SHA256_COMPRESS_COLS: usize = size_of::<Sha256CompressCols<u8>>();

impl<T> Borrow<Sha256Cols<T>> for [T] {
    fn borrow(&self) -> &Sha256Cols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_AIR_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<Sha256Cols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

impl<T> BorrowMut<Sha256Cols<T>> for [T] {
    fn borrow_mut(&mut self) -> &mut Sha256Cols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_AIR_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to_mut::<Sha256Cols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &mut shorts[0]
    }
}

impl<T> Borrow<Sha256CompressCols<T>> for [T] {
    fn borrow(&self) -> &Sha256CompressCols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_COMPRESS_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<Sha256CompressCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

impl<T> BorrowMut<Sha256CompressCols<T>> for [T] {
    fn borrow_mut(&mut self) -> &mut Sha256CompressCols<T> {
        debug_assert_eq!(self.len(), NUM_SHA256_COMPRESS_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to_mut::<Sha256CompressCols<T>>() };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &mut shorts[0]
    }
}
