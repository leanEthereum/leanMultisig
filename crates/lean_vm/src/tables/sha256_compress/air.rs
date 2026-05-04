use backend::*;

use super::{
    NUM_SHA256_COMPRESS_COLS, SHA256_BLOCK_WORDS, SHA256_CHAIN_LEN, SHA256_K, SHA256_PRECOMPILE_DATA,
    SHA256_SCHEDULE_EXTENSIONS, SHA256_U32_LIMBS, SHA256_WORD_BITS, Sha256Cols, Sha256CompressCols,
    Sha256CompressPrecompile,
};
use crate::{EF, ExtraDataForBuses, eval_virtual_bus_column};

const BITS_PER_LIMB: usize = 16;

impl<const BUS: bool> Air for Sha256CompressPrecompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;

    fn n_columns(&self) -> usize {
        NUM_SHA256_COMPRESS_COLS
    }

    fn degree_air(&self) -> usize {
        3
    }

    fn n_constraints(&self) -> usize {
        7840 + 32 + 1 + BUS as usize
    }

    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cols: &Sha256CompressCols<AB::IF> = {
            let up = builder.up();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Sha256CompressCols<AB::IF>>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert!(suffix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            unsafe { &*shorts.as_ptr() }
        };

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag,
                &[
                    AB::IF::from_usize(SHA256_PRECOMPILE_DATA),
                    cols.state_ptr,
                    cols.block_ptr,
                    cols.out_ptr,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[
                AB::IF::from_usize(SHA256_PRECOMPILE_DATA),
                cols.state_ptr,
                cols.block_ptr,
                cols.out_ptr,
            ]);
        }

        builder.assert_bool(cols.flag);
        eval_sha256_air(builder, &cols.sha);
        eval_block_limb_bridges(builder, &cols);
    }
}

fn eval_sha256_air<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::IF>) {
    eval_bit_range_checks(builder, local);
    eval_initial_state(builder, local);
    eval_message_schedule(builder, local);
    eval_compression(builder, local);
    eval_finalization(builder, local);
}

fn eval_bit_range_checks<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::IF>) {
    for word in &local.w {
        assert_bools(builder, word);
    }
    for word in &local.a_chain {
        assert_bools(builder, word);
    }
    for word in &local.e_chain {
        assert_bools(builder, word);
    }
}

fn eval_initial_state<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::IF>) {
    for i in 0..4 {
        let chain_idx = 3 - i;
        assert_packed_equals_bits(builder, &local.h_in[i], &local.a_chain[chain_idx]);
    }
    for i in 0..4 {
        let chain_idx = 3 - i;
        assert_packed_equals_bits(builder, &local.h_in[4 + i], &local.e_chain[chain_idx]);
    }
}

fn eval_block_limb_bridges<AB: AirBuilder>(builder: &mut AB, cols: &Sha256CompressCols<AB::IF>) {
    for i in 0..SHA256_BLOCK_WORDS {
        assert_packed_equals_bits(builder, &cols.block_limbs[i], &cols.sha.w[i]);
    }
}

fn eval_message_schedule<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::IF>) {
    for i in 0..SHA256_SCHEDULE_EXTENSIONS {
        let t = i + SHA256_BLOCK_WORDS;

        assert_sigma_matches(
            builder,
            &local.w[t - 15],
            SigmaSpec::SmallSigma0,
            &local.sched_sigma0[i],
        );
        assert_sigma_matches(builder, &local.w[t - 2], SigmaSpec::SmallSigma1, &local.sched_sigma1[i]);

        let w_tm7_packed = pack_word::<AB>(&local.w[t - 7]);
        add2(builder, &local.sched_tmp[i], &local.sched_sigma1[i], &w_tm7_packed);

        let w_t_packed = pack_word::<AB>(&local.w[t]);
        let sched_sigma0 = local.sched_sigma0[i];
        let w_tm16_packed = pack_word::<AB>(&local.w[t - 16]);
        add3_expr_out(builder, &w_t_packed, &local.sched_tmp[i], &sched_sigma0, &w_tm16_packed);
    }
}

fn eval_compression<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::IF>) {
    for (t, round) in local.rounds.iter().enumerate() {
        let a_bits = &local.a_chain[t + 3];
        let b_bits = &local.a_chain[t + 2];
        let c_bits = &local.a_chain[t + 1];
        let d_bits = &local.a_chain[t];
        let e_bits = &local.e_chain[t + 3];
        let f_bits = &local.e_chain[t + 2];
        let g_bits = &local.e_chain[t + 1];
        let h_bits = &local.e_chain[t];

        assert_sigma_matches(builder, e_bits, SigmaSpec::BigSigma1, &round.sigma1_e);
        assert_ch_matches(builder, e_bits, f_bits, g_bits, &round.ch);

        let h_packed = pack_word::<AB>(h_bits);
        add3(builder, &round.tmp1, &round.sigma1_e, &round.ch, &h_packed);

        let k = [
            AB::IF::from_u32(SHA256_K[t] & 0xffff),
            AB::IF::from_u32(SHA256_K[t] >> BITS_PER_LIMB),
        ];
        let w_packed = pack_word::<AB>(&local.w[t]);
        add3(builder, &round.t1, &round.tmp1, &k, &w_packed);

        assert_sigma_matches(builder, a_bits, SigmaSpec::BigSigma0, &round.sigma0_a);
        assert_maj_matches(builder, a_bits, b_bits, c_bits, &round.maj);

        let new_a_packed = pack_word::<AB>(&local.a_chain[t + 4]);
        add3_expr_out(builder, &new_a_packed, &round.t1, &round.sigma0_a, &round.maj);

        let new_e_packed = pack_word::<AB>(&local.e_chain[t + 4]);
        let d_packed = pack_word::<AB>(d_bits);
        add2_expr_out(builder, &new_e_packed, &round.t1, &d_packed);
    }
}

fn eval_finalization<AB: AirBuilder>(builder: &mut AB, local: &Sha256Cols<AB::IF>) {
    for i in 0..4 {
        let final_bits = &local.a_chain[SHA256_CHAIN_LEN - 1 - i];
        let packed = pack_word::<AB>(final_bits);
        add2(builder, &local.h_out[i], &local.h_in[i], &packed);
    }
    for i in 0..4 {
        let final_bits = &local.e_chain[SHA256_CHAIN_LEN - 1 - i];
        let packed = pack_word::<AB>(final_bits);
        add2(builder, &local.h_out[4 + i], &local.h_in[4 + i], &packed);
    }
}

#[inline]
fn assert_bools<AB: AirBuilder>(builder: &mut AB, bits: &[AB::IF; SHA256_WORD_BITS]) {
    for &bit in bits {
        builder.assert_bool(bit);
    }
}

#[inline]
fn pack_word<AB: AirBuilder>(bits: &[AB::IF; SHA256_WORD_BITS]) -> [AB::IF; SHA256_U32_LIMBS] {
    [
        pack_bits_le::<AB>(&bits[..BITS_PER_LIMB]),
        pack_bits_le::<AB>(&bits[BITS_PER_LIMB..]),
    ]
}

#[inline]
fn pack_bits_le<AB: AirBuilder>(bits: &[AB::IF]) -> AB::IF {
    let mut acc = AB::IF::ZERO;
    for &bit in bits.iter().rev() {
        acc = acc.double() + bit;
    }
    acc
}

#[inline]
fn assert_packed_equals_bits<AB: AirBuilder>(
    builder: &mut AB,
    packed: &[AB::IF; SHA256_U32_LIMBS],
    bits: &[AB::IF; SHA256_WORD_BITS],
) {
    let built = pack_word::<AB>(bits);
    builder.assert_zero(packed[0] - built[0]);
    builder.assert_zero(packed[1] - built[1]);
}

#[inline]
fn add2<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::IF; SHA256_U32_LIMBS],
    b: &[AB::IF; SHA256_U32_LIMBS],
    c: &[AB::IF; SHA256_U32_LIMBS],
) {
    add2_expr_out(builder, a, b, c);
}

#[inline]
fn add3<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::IF; SHA256_U32_LIMBS],
    b: &[AB::IF; SHA256_U32_LIMBS],
    c: &[AB::IF; SHA256_U32_LIMBS],
    d: &[AB::IF; SHA256_U32_LIMBS],
) {
    add3_expr_out(builder, a, b, c, d);
}

#[inline]
fn add2_expr_out<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::IF; SHA256_U32_LIMBS],
    b: &[AB::IF; SHA256_U32_LIMBS],
    c: &[AB::IF; SHA256_U32_LIMBS],
) {
    let two_16 = AB::IF::from_usize(1 << BITS_PER_LIMB);
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0];
    let acc_32 = a[1] - b[1] - c[1];
    let acc = acc_16 + acc_32 * two_16;

    builder.assert_zero(acc * (acc + two_32));
    builder.assert_zero(acc_16 * (acc_16 + two_16));
}

#[inline]
fn add3_expr_out<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::IF; SHA256_U32_LIMBS],
    b: &[AB::IF; SHA256_U32_LIMBS],
    c: &[AB::IF; SHA256_U32_LIMBS],
    d: &[AB::IF; SHA256_U32_LIMBS],
) {
    let two_16 = AB::IF::from_usize(1 << BITS_PER_LIMB);
    let two_32 = two_16.square();

    let acc_16 = a[0] - b[0] - c[0] - d[0];
    let acc_32 = a[1] - b[1] - c[1] - d[1];
    let acc = acc_16 + acc_32 * two_16;

    builder.assert_zero(acc * (acc + two_32) * (acc + two_32.double()));
    builder.assert_zero(acc_16 * (acc_16 + two_16) * (acc_16 + two_16.double()));
}

#[derive(Copy, Clone)]
enum SigmaSpec {
    BigSigma0,
    BigSigma1,
    SmallSigma0,
    SmallSigma1,
}

#[derive(Copy, Clone)]
enum ShiftKind {
    Rotate,
    Logical,
}

#[inline]
const fn sigma_params(spec: SigmaSpec) -> (usize, usize, usize, ShiftKind) {
    match spec {
        SigmaSpec::BigSigma0 => (2, 13, 22, ShiftKind::Rotate),
        SigmaSpec::BigSigma1 => (6, 11, 25, ShiftKind::Rotate),
        SigmaSpec::SmallSigma0 => (7, 18, 3, ShiftKind::Logical),
        SigmaSpec::SmallSigma1 => (17, 19, 10, ShiftKind::Logical),
    }
}

fn assert_sigma_matches<AB: AirBuilder>(
    builder: &mut AB,
    bits: &[AB::IF; SHA256_WORD_BITS],
    spec: SigmaSpec,
    packed: &[AB::IF; SHA256_U32_LIMBS],
) {
    let (r1, r2, r3, kind) = sigma_params(spec);
    let mut built = [AB::IF::ZERO; SHA256_U32_LIMBS];
    for (limb, slot) in built.iter_mut().enumerate() {
        let lo = limb * BITS_PER_LIMB;
        let hi = lo + BITS_PER_LIMB;
        let mut acc = AB::IF::ZERO;
        for i in (lo..hi).rev() {
            let b1 = bits[(i + r1) % SHA256_WORD_BITS];
            let b2 = bits[(i + r2) % SHA256_WORD_BITS];
            let b3 = match kind {
                ShiftKind::Rotate => bits[(i + r3) % SHA256_WORD_BITS],
                ShiftKind::Logical => {
                    let src = i + r3;
                    if src < SHA256_WORD_BITS {
                        bits[src]
                    } else {
                        AB::IF::ZERO
                    }
                }
            };
            acc = acc.double() + b1.xor3(&b2, &b3);
        }
        *slot = acc;
    }

    builder.assert_zero(packed[0] - built[0]);
    builder.assert_zero(packed[1] - built[1]);
}

fn assert_ch_matches<AB: AirBuilder>(
    builder: &mut AB,
    e: &[AB::IF; SHA256_WORD_BITS],
    f: &[AB::IF; SHA256_WORD_BITS],
    g: &[AB::IF; SHA256_WORD_BITS],
    packed: &[AB::IF; SHA256_U32_LIMBS],
) {
    let mut built = [AB::IF::ZERO; SHA256_U32_LIMBS];
    for (limb, slot) in built.iter_mut().enumerate() {
        let lo = limb * BITS_PER_LIMB;
        let hi = lo + BITS_PER_LIMB;
        let mut acc = AB::IF::ZERO;
        for i in (lo..hi).rev() {
            let ei = e[i];
            let ch_i = ei * f[i] + (AB::IF::ONE - ei) * g[i];
            acc = acc.double() + ch_i;
        }
        *slot = acc;
    }

    builder.assert_zero(packed[0] - built[0]);
    builder.assert_zero(packed[1] - built[1]);
}

fn assert_maj_matches<AB: AirBuilder>(
    builder: &mut AB,
    a: &[AB::IF; SHA256_WORD_BITS],
    b: &[AB::IF; SHA256_WORD_BITS],
    c: &[AB::IF; SHA256_WORD_BITS],
    packed: &[AB::IF; SHA256_U32_LIMBS],
) {
    let mut built = [AB::IF::ZERO; SHA256_U32_LIMBS];
    for (limb, slot) in built.iter_mut().enumerate() {
        let lo = limb * BITS_PER_LIMB;
        let hi = lo + BITS_PER_LIMB;
        let mut acc = AB::IF::ZERO;
        for i in (lo..hi).rev() {
            let maj_i = a[i] * b[i] + c[i] * a[i].xor(&b[i]);
            acc = acc.double() + maj_i;
        }
        *slot = acc;
    }

    builder.assert_zero(packed[0] - built[0]);
    builder.assert_zero(packed[1] - built[1]);
}
