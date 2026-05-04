use core::borrow::BorrowMut;

use backend::PrimeCharacteristicRing;

use crate::{F, TableTrace};

use super::{
    SHA256_BLOCK_WORDS, SHA256_COMPRESS_ROUNDS, SHA256_SCHEDULE_EXTENSIONS, SHA256_STATE_WORDS, Sha256Cols,
    Sha256CompressCols, Sha256CompressionWitness, Sha256RoundCols, generate_sha256_compression_witness, u32_to_bits_le,
    u32_to_u16_limbs_le,
};

pub fn sha256_compress_trace_row(
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    h_in: [u32; SHA256_STATE_WORDS],
    block: [u32; SHA256_BLOCK_WORDS],
) -> Vec<F> {
    let witness = generate_sha256_compression_witness(h_in, block);
    sha256_compress_trace_row_from_witness(flag, state_ptr, block_ptr, out_ptr, &witness)
}

pub fn sha256_compress_trace_row_from_witness(
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    witness: &Sha256CompressionWitness,
) -> Vec<F> {
    let mut row = F::zero_vec(super::NUM_SHA256_COMPRESS_COLS);
    let cols: &mut Sha256CompressCols<F> = row.as_mut_slice().borrow_mut();
    fill_sha256_compress_cols(cols, flag, state_ptr, block_ptr, out_ptr, witness);
    row
}

pub fn push_sha256_compress_trace_row(
    trace: &mut TableTrace,
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    h_in: [u32; SHA256_STATE_WORDS],
    block: [u32; SHA256_BLOCK_WORDS],
) {
    let row = sha256_compress_trace_row(flag, state_ptr, block_ptr, out_ptr, h_in, block);
    push_row(trace, row);
}

pub fn push_sha256_compress_trace_row_from_witness(
    trace: &mut TableTrace,
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    witness: &Sha256CompressionWitness,
) {
    let row = sha256_compress_trace_row_from_witness(flag, state_ptr, block_ptr, out_ptr, witness);
    push_row(trace, row);
}

fn push_row(trace: &mut TableTrace, row: Vec<F>) {
    debug_assert_eq!(trace.columns.len(), row.len());
    for (column, value) in trace.columns.iter_mut().zip(row) {
        column.push(value);
    }
}

pub fn fill_sha256_compress_cols(
    cols: &mut Sha256CompressCols<F>,
    flag: F,
    state_ptr: F,
    block_ptr: F,
    out_ptr: F,
    witness: &Sha256CompressionWitness,
) {
    cols.flag = flag;
    cols.state_ptr = state_ptr;
    cols.block_ptr = block_ptr;
    cols.out_ptr = out_ptr;

    for (dst, &word) in cols.block_limbs.iter_mut().zip(&witness.block) {
        *dst = word_limbs(word);
    }

    fill_sha256_air_cols(&mut cols.sha, witness);
}

pub fn fill_sha256_air_cols(cols: &mut Sha256Cols<F>, witness: &Sha256CompressionWitness) {
    for i in 0..SHA256_STATE_WORDS {
        cols.h_in[i] = word_limbs(witness.h_in[i]);
        cols.h_out[i] = word_limbs(witness.h_out[i]);
    }

    for i in 0..(4 + SHA256_COMPRESS_ROUNDS) {
        cols.a_chain[i] = word_bits(witness.a_chain[i]);
        cols.e_chain[i] = word_bits(witness.e_chain[i]);
    }

    for i in 0..SHA256_COMPRESS_ROUNDS {
        cols.w[i] = word_bits(witness.w[i]);
        cols.rounds[i] = Sha256RoundCols {
            sigma1_e: word_limbs(witness.rounds[i].sigma1_e),
            ch: word_limbs(witness.rounds[i].ch),
            tmp1: word_limbs(witness.rounds[i].tmp1),
            t1: word_limbs(witness.rounds[i].t1),
            sigma0_a: word_limbs(witness.rounds[i].sigma0_a),
            maj: word_limbs(witness.rounds[i].maj),
        };
    }

    for i in 0..SHA256_SCHEDULE_EXTENSIONS {
        cols.sched_sigma0[i] = word_limbs(witness.sched_sigma0[i]);
        cols.sched_sigma1[i] = word_limbs(witness.sched_sigma1[i]);
        cols.sched_tmp[i] = word_limbs(witness.sched_tmp[i]);
    }
}

fn word_limbs(word: u32) -> [F; 2] {
    u32_to_u16_limbs_le(word).map(|limb| F::from_usize(usize::from(limb)))
}

fn word_bits(word: u32) -> [F; 32] {
    u32_to_bits_le(word).map(F::from_bool)
}
