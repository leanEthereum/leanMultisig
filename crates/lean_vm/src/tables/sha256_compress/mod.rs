use crate::{F, PrecompileCompTimeArgs, RunnerError, Table};
use backend::{PrimeCharacteristicRing, PrimeField32};
use utils::ToUsize;

mod air;

mod columns;
pub use columns::*;

mod trace_gen;
pub use trace_gen::*;

pub const SHA256_STATE_WORDS: usize = 8;
pub const SHA256_BLOCK_WORDS: usize = 16;
pub const SHA256_INPUT_WORDS: usize = SHA256_BLOCK_WORDS + SHA256_STATE_WORDS;
pub const SHA256_WORD_BITS: usize = 32;
pub const SHA256_U32_LIMBS: usize = 2;
pub const SHA256_COMPRESS_ROUNDS: usize = 64;
pub const SHA256_SCHEDULE_EXTENSIONS: usize = SHA256_COMPRESS_ROUNDS - SHA256_BLOCK_WORDS;

pub const SHA256_STATE_LIMBS: usize = SHA256_STATE_WORDS * SHA256_U32_LIMBS;
pub const SHA256_BLOCK_LIMBS: usize = SHA256_BLOCK_WORDS * SHA256_U32_LIMBS;

pub const SHA256_IV: [u32; SHA256_STATE_WORDS] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

pub const SHA256_ABC_BLOCK: [u32; SHA256_BLOCK_WORDS] = [0x61626380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x18];

pub const SHA256_ZERO_BLOCK: [u32; SHA256_BLOCK_WORDS] = [0; SHA256_BLOCK_WORDS];

pub const SHA256_PRECOMPILE_DATA: usize = 5;
pub const SHA256_COMPRESS_NAME: &str = "sha256_compress";

const SHA256_K: [u32; SHA256_COMPRESS_ROUNDS] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sha256RoundWitness {
    pub sigma1_e: u32,
    pub ch: u32,
    pub tmp1: u32,
    pub t1: u32,
    pub sigma0_a: u32,
    pub maj: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sha256CompressionWitness {
    pub h_in: [u32; SHA256_STATE_WORDS],
    pub block: [u32; SHA256_BLOCK_WORDS],
    pub w: [u32; SHA256_COMPRESS_ROUNDS],
    pub sched_sigma0: [u32; SHA256_SCHEDULE_EXTENSIONS],
    pub sched_sigma1: [u32; SHA256_SCHEDULE_EXTENSIONS],
    pub sched_tmp: [u32; SHA256_SCHEDULE_EXTENSIONS],
    pub a_chain: [u32; 4 + SHA256_COMPRESS_ROUNDS],
    pub e_chain: [u32; 4 + SHA256_COMPRESS_ROUNDS],
    pub rounds: [Sha256RoundWitness; SHA256_COMPRESS_ROUNDS],
    pub h_out: [u32; SHA256_STATE_WORDS],
}

pub fn generate_sha256_compression_witness(
    h_in: [u32; SHA256_STATE_WORDS],
    block: [u32; SHA256_BLOCK_WORDS],
) -> Sha256CompressionWitness {
    let mut w = [0u32; SHA256_COMPRESS_ROUNDS];
    w[..SHA256_BLOCK_WORDS].copy_from_slice(&block);

    let mut sched_sigma0 = [0u32; SHA256_SCHEDULE_EXTENSIONS];
    let mut sched_sigma1 = [0u32; SHA256_SCHEDULE_EXTENSIONS];
    let mut sched_tmp = [0u32; SHA256_SCHEDULE_EXTENSIONS];

    for t in SHA256_BLOCK_WORDS..SHA256_COMPRESS_ROUNDS {
        let i = t - SHA256_BLOCK_WORDS;
        let s0 = small_sigma0(w[t - 15]);
        let s1 = small_sigma1(w[t - 2]);
        let tmp = s1.wrapping_add(w[t - 7]);
        w[t] = tmp.wrapping_add(s0).wrapping_add(w[t - 16]);
        sched_sigma0[i] = s0;
        sched_sigma1[i] = s1;
        sched_tmp[i] = tmp;
    }

    let mut a_chain = [0u32; 4 + SHA256_COMPRESS_ROUNDS];
    let mut e_chain = [0u32; 4 + SHA256_COMPRESS_ROUNDS];
    a_chain[0] = h_in[3];
    a_chain[1] = h_in[2];
    a_chain[2] = h_in[1];
    a_chain[3] = h_in[0];
    e_chain[0] = h_in[7];
    e_chain[1] = h_in[6];
    e_chain[2] = h_in[5];
    e_chain[3] = h_in[4];

    let empty_round = Sha256RoundWitness {
        sigma1_e: 0,
        ch: 0,
        tmp1: 0,
        t1: 0,
        sigma0_a: 0,
        maj: 0,
    };
    let mut rounds = [empty_round; SHA256_COMPRESS_ROUNDS];
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = h_in;

    for t in 0..SHA256_COMPRESS_ROUNDS {
        let sigma1_e = big_sigma1(e);
        let ch = ch(e, f, g);
        let tmp1 = h.wrapping_add(sigma1_e).wrapping_add(ch);
        let t1 = tmp1.wrapping_add(SHA256_K[t]).wrapping_add(w[t]);
        let sigma0_a = big_sigma0(a);
        let maj = maj(a, b, c);
        let new_a = t1.wrapping_add(sigma0_a).wrapping_add(maj);
        let new_e = d.wrapping_add(t1);

        rounds[t] = Sha256RoundWitness {
            sigma1_e,
            ch,
            tmp1,
            t1,
            sigma0_a,
            maj,
        };
        a_chain[t + 4] = new_a;
        e_chain[t + 4] = new_e;

        h = g;
        g = f;
        f = e;
        e = new_e;
        d = c;
        c = b;
        b = a;
        a = new_a;
    }

    let final_state = [a, b, c, d, e, f, g, h];
    let h_out = core::array::from_fn(|i| h_in[i].wrapping_add(final_state[i]));

    Sha256CompressionWitness {
        h_in,
        block,
        w,
        sched_sigma0,
        sched_sigma1,
        sched_tmp,
        a_chain,
        e_chain,
        rounds,
        h_out,
    }
}

pub fn sha256_compress_words(
    h_in: [u32; SHA256_STATE_WORDS],
    block: [u32; SHA256_BLOCK_WORDS],
) -> [u32; SHA256_STATE_WORDS] {
    generate_sha256_compression_witness(h_in, block).h_out
}

pub const fn u32_to_u16_limbs_le(word: u32) -> [u16; SHA256_U32_LIMBS] {
    [(word & 0xffff) as u16, (word >> 16) as u16]
}

pub const fn u16_limbs_le_to_u32(limbs: [u16; SHA256_U32_LIMBS]) -> u32 {
    limbs[0] as u32 | ((limbs[1] as u32) << 16)
}

pub fn words_to_u16_limbs_le(words: impl IntoIterator<Item = u32>) -> Vec<u16> {
    let mut limbs = Vec::new();
    for word in words {
        let word_limbs = u32_to_u16_limbs_le(word);
        limbs.extend_from_slice(&word_limbs);
    }
    limbs
}

pub fn words_to_field_limbs_le<const N: usize>(words: [u32; N]) -> Vec<F> {
    words_to_u16_limbs_le(words)
        .into_iter()
        .map(|limb| F::from_usize(usize::from(limb)))
        .collect()
}

pub fn u32_to_bits_le(word: u32) -> [bool; SHA256_WORD_BITS] {
    core::array::from_fn(|i| ((word >> i) & 1) == 1)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sha256CompressPrecompile<const BUS: bool>;

impl<const BUS: bool> crate::TableT for Sha256CompressPrecompile<BUS> {
    fn name(&self) -> &'static str {
        SHA256_COMPRESS_NAME
    }

    fn table(&self) -> Table {
        Table::sha256_compress()
    }

    fn lookups(&self) -> Vec<crate::LookupIntoMemory> {
        vec![
            crate::LookupIntoMemory {
                index: SHA256_COL_STATE_PTR,
                values: (SHA256_COL_STATE_LIMBS_START..SHA256_COL_STATE_LIMBS_START + SHA256_STATE_LIMBS).collect(),
            },
            crate::LookupIntoMemory {
                index: SHA256_COL_BLOCK_PTR,
                values: (SHA256_COL_BLOCK_LIMBS_START..SHA256_COL_BLOCK_LIMBS_START + SHA256_BLOCK_LIMBS).collect(),
            },
            crate::LookupIntoMemory {
                index: SHA256_COL_OUT_PTR,
                values: (SHA256_COL_OUT_LIMBS_START..SHA256_COL_OUT_LIMBS_START + SHA256_STATE_LIMBS).collect(),
            },
        ]
    }

    fn bus(&self) -> crate::Bus {
        crate::Bus {
            direction: crate::BusDirection::Pull,
            selector: SHA256_COL_FLAG,
            data: vec![
                crate::BusData::Constant(SHA256_PRECOMPILE_DATA),
                crate::BusData::Column(SHA256_COL_STATE_PTR),
                crate::BusData::Column(SHA256_COL_BLOCK_PTR),
                crate::BusData::Column(SHA256_COL_OUT_PTR),
            ],
        }
    }

    fn padding_row(&self, padding: &crate::PaddingMemory) -> Vec<F> {
        sha256_compress_trace_row(
            F::ZERO,
            F::from_usize(padding.sha256_state_ptr),
            F::from_usize(padding.sha256_block_ptr),
            F::from_usize(padding.sha256_out_ptr),
            SHA256_IV,
            SHA256_ZERO_BLOCK,
        )
    }

    fn execute<M: crate::MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut crate::InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Sha256Compress = args else {
            unreachable!("Sha256Compress table called with non-Sha256Compress args");
        };

        let state_ptr = arg_a.to_usize();
        let block_ptr = arg_b.to_usize();
        let out_ptr = arg_c.to_usize();

        let h_in = field_limbs_to_words::<SHA256_STATE_WORDS>(&ctx.memory.get_slice(state_ptr, SHA256_STATE_LIMBS)?)?;
        let block = field_limbs_to_words::<SHA256_BLOCK_WORDS>(&ctx.memory.get_slice(block_ptr, SHA256_BLOCK_LIMBS)?)?;
        let witness = generate_sha256_compression_witness(h_in, block);
        ctx.memory.set_slice(out_ptr, &words_to_field_limbs_le(witness.h_out))?;

        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        push_sha256_compress_trace_row_from_witness(trace, F::ONE, arg_a, arg_b, arg_c, &witness);

        Ok(())
    }
}

fn field_limbs_to_words<const N: usize>(limbs: &[F]) -> Result<[u32; N], RunnerError> {
    assert_eq!(limbs.len(), N * SHA256_U32_LIMBS);
    let mut words = [0u32; N];
    for (word, limb_pair) in words.iter_mut().zip(limbs.chunks_exact(SHA256_U32_LIMBS)) {
        let lo = limb_to_u16(limb_pair[0])?;
        let hi = limb_to_u16(limb_pair[1])?;
        *word = u16_limbs_le_to_u32([lo, hi]);
    }
    Ok(words)
}

fn limb_to_u16(limb: F) -> Result<u16, RunnerError> {
    let value = limb.as_canonical_u32();
    u16::try_from(value).map_err(|_| RunnerError::InvalidSha256Input)
}

#[inline]
const fn small_sigma0(x: u32) -> u32 {
    x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3)
}

#[inline]
const fn small_sigma1(x: u32) -> u32 {
    x.rotate_right(17) ^ x.rotate_right(19) ^ (x >> 10)
}

#[inline]
const fn big_sigma0(x: u32) -> u32 {
    x.rotate_right(2) ^ x.rotate_right(13) ^ x.rotate_right(22)
}

#[inline]
const fn big_sigma1(x: u32) -> u32 {
    x.rotate_right(6) ^ x.rotate_right(11) ^ x.rotate_right(25)
}

#[inline]
const fn ch(e: u32, f: u32, g: u32) -> u32 {
    (e & f) ^ ((!e) & g)
}

#[inline]
const fn maj(a: u32, b: u32, c: u32) -> u32 {
    (a & b) ^ (a & c) ^ (b & c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use backend::{
        Air, PrimeCharacteristicRing, PrimeField32, SumcheckComputation, get_symbolic_constraints_and_bus_data_values,
    };
    use core::borrow::Borrow;
    use std::collections::BTreeMap;

    use crate::{
        EF, ExtraDataForBuses, InstructionContext, InstructionCounts, Memory, MemoryAccess, TableT, TableTrace,
    };

    fn words_to_hex(words: [u32; SHA256_STATE_WORDS]) -> String {
        words.iter().map(|word| format!("{word:08x}")).collect()
    }

    fn extract_packed_words(limbs: &[[F; SHA256_U32_LIMBS]; SHA256_STATE_WORDS]) -> [u32; SHA256_STATE_WORDS] {
        core::array::from_fn(|i| {
            let lo = limbs[i][0].as_canonical_u32();
            let hi = limbs[i][1].as_canonical_u32();
            lo | (hi << 16)
        })
    }

    fn extract_trace_output(row: &[F]) -> [u32; SHA256_STATE_WORDS] {
        let cols: &Sha256CompressCols<F> = row.borrow();
        extract_packed_words(&cols.sha.h_out)
    }

    fn sha2_compress_reference(
        block: [u32; SHA256_BLOCK_WORDS],
        h_in: [u32; SHA256_STATE_WORDS],
    ) -> [u32; SHA256_STATE_WORDS] {
        let mut block_bytes = [0u8; 64];
        for (i, word) in block.iter().enumerate() {
            block_bytes[i * 4..i * 4 + 4].copy_from_slice(&word.to_be_bytes());
        }
        let mut state = h_in;
        sha2::block_api::compress256(&mut state, core::slice::from_ref(&block_bytes));
        state
    }

    fn air_extra_data(n_constraints: usize) -> ExtraDataForBuses<EF> {
        let mut powers = Vec::with_capacity(n_constraints + 1);
        let alpha = EF::from(F::from_usize(7));
        let mut current = EF::ONE;
        for _ in 0..=n_constraints {
            powers.push(current);
            current *= alpha;
        }
        ExtraDataForBuses::new(Vec::new(), EF::ZERO, powers)
    }

    #[test]
    fn abc_single_block_matches_known_digest() {
        let out = sha256_compress_words(SHA256_IV, SHA256_ABC_BLOCK);
        assert_eq!(
            words_to_hex(out),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn low_then_high_limb_order_is_locked() {
        assert_eq!(u32_to_u16_limbs_le(0x61626380), [0x6380, 0x6162]);
        assert_eq!(u32_to_u16_limbs_le(0x18), [0x0018, 0x0000]);
        assert_eq!(u16_limbs_le_to_u32([0x6380, 0x6162]), 0x61626380);
    }

    #[test]
    fn column_counts_match_plonky3_baseline_plus_leanvm_prefix() {
        assert_eq!(NUM_SHA256_AIR_COLS, 7488);
        assert_eq!(SHA256_COL_AIR_START, 36);
        assert_eq!(NUM_SHA256_COMPRESS_COLS, 7524);
    }

    #[test]
    fn trace_row_populates_prefix_block_and_output() {
        let row = sha256_compress_trace_row(
            F::ONE,
            F::from_usize(10),
            F::from_usize(20),
            F::from_usize(30),
            SHA256_IV,
            SHA256_ABC_BLOCK,
        );
        assert_eq!(row.len(), NUM_SHA256_COMPRESS_COLS);

        let cols: &Sha256CompressCols<F> = row.as_slice().borrow();
        assert_eq!(cols.flag, F::ONE);
        assert_eq!(cols.state_ptr, F::from_usize(10));
        assert_eq!(cols.block_ptr, F::from_usize(20));
        assert_eq!(cols.out_ptr, F::from_usize(30));
        assert_eq!(cols.block_limbs[0], [F::from_usize(0x6380), F::from_usize(0x6162)]);
        assert_eq!(cols.block_limbs[15], [F::from_usize(0x18), F::ZERO]);

        assert_eq!(
            words_to_hex(extract_packed_words(&cols.sha.h_out)),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn trace_generation_matches_sha2_compress_reference() {
        let cases = [
            (SHA256_IV, SHA256_ABC_BLOCK),
            (SHA256_IV, SHA256_ZERO_BLOCK),
            (
                [
                    0x0123_4567,
                    0x89ab_cdef,
                    0xfedc_ba98,
                    0x7654_3210,
                    0x0f1e_2d3c,
                    0x4b5a_6978,
                    0x8877_6655,
                    0x4433_2211,
                ],
                [
                    0xffff_ffff,
                    0,
                    0x1357_9bdf,
                    0x2468_ace0,
                    0xdead_beef,
                    0xcafe_babe,
                    0x0001_0002,
                    0x0003_0004,
                    0x0102_0304,
                    0x1111_2222,
                    0x3333_4444,
                    0x5555_6666,
                    0x7777_8888,
                    0x9999_aaaa,
                    0xbbbb_cccc,
                    0xdddd_eeee,
                ],
            ),
        ];

        for (h_in, block) in cases {
            let row = sha256_compress_trace_row(F::ONE, F::ZERO, F::ZERO, F::ZERO, h_in, block);
            assert_eq!(extract_trace_output(&row), sha2_compress_reference(block, h_in));
        }
    }

    #[test]
    fn symbolic_constraint_count_matches_declared_count() {
        let table = Sha256CompressPrecompile::<false>;
        let (constraints, bus_flag, bus_data) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
        assert_eq!(constraints.len(), table.n_constraints());
        assert_eq!(
            bus_flag,
            backend::SymbolicExpression::Variable(backend::SymbolicVariable::new(SHA256_COL_FLAG))
        );
        assert_eq!(bus_data.len(), 4);
    }

    #[test]
    fn generated_trace_row_satisfies_air_and_tampered_row_fails() {
        let table = Sha256CompressPrecompile::<false>;
        let extra_data = air_extra_data(table.n_constraints());
        let row = sha256_compress_trace_row(
            F::ONE,
            F::from_usize(10),
            F::from_usize(20),
            F::from_usize(30),
            SHA256_IV,
            SHA256_ABC_BLOCK,
        );

        assert_eq!(
            <Sha256CompressPrecompile<false> as SumcheckComputation<EF>>::eval_base(&table, &row, &extra_data),
            EF::ZERO
        );

        let mut tampered = row;
        tampered[SHA256_COL_AIR_START] = F::TWO;
        assert_ne!(
            <Sha256CompressPrecompile<false> as SumcheckComputation<EF>>::eval_base(&table, &tampered, &extra_data),
            EF::ZERO
        );
    }

    #[test]
    fn precompile_execute_writes_output_and_trace_row() {
        let state_ptr = 0;
        let block_ptr = SHA256_STATE_LIMBS;
        let out_ptr = SHA256_STATE_LIMBS + SHA256_BLOCK_LIMBS;

        let mut memory = Memory::new(vec![]);
        memory
            .set_slice(state_ptr, &words_to_field_limbs_le(SHA256_IV))
            .unwrap();
        memory
            .set_slice(block_ptr, &words_to_field_limbs_le(SHA256_ABC_BLOCK))
            .unwrap();

        let table = Table::sha256_compress();
        let mut traces = BTreeMap::new();
        traces.insert(table, TableTrace::new(&Sha256CompressPrecompile::<true>));
        let mut fp = 0;
        let mut pc = 0;
        let pcs = vec![0];
        let mut counts = InstructionCounts::default();
        let mut ctx = InstructionContext {
            memory: &mut memory,
            fp: &mut fp,
            pc: &mut pc,
            pcs: &pcs,
            traces: &mut traces,
            counts: &mut counts,
        };

        table
            .execute(
                F::from_usize(state_ptr),
                F::from_usize(block_ptr),
                F::from_usize(out_ptr),
                PrecompileCompTimeArgs::Sha256Compress,
                &mut ctx,
            )
            .unwrap();

        let out = ctx.memory.get_slice(out_ptr, SHA256_STATE_LIMBS).unwrap();
        let out_words = field_limbs_to_words::<SHA256_STATE_WORDS>(&out).unwrap();
        assert_eq!(
            words_to_hex(out_words),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );

        let trace = ctx.traces.get(&table).unwrap();
        assert_eq!(trace.columns.len(), NUM_SHA256_COMPRESS_COLS);
        assert_eq!(trace.columns[SHA256_COL_FLAG], [F::ONE]);
        assert_eq!(trace.columns[SHA256_COL_STATE_PTR], [F::from_usize(state_ptr)]);
        assert_eq!(trace.columns[SHA256_COL_BLOCK_PTR], [F::from_usize(block_ptr)]);
        assert_eq!(trace.columns[SHA256_COL_OUT_PTR], [F::from_usize(out_ptr)]);
    }
}
