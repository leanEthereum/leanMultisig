use crate::execution::memory::MemoryAccess;
use crate::*;
use backend::*;
use utils::{ToUsize, poseidon8_compress};

mod sparse;
mod trace_gen;
pub use trace_gen::fill_trace_poseidon_8;

use sparse::{PARTIAL_ROUNDS as SPARSE_PARTIAL_ROUNDS, get_partial_constants};

pub(super) const WIDTH: usize = 8;
pub(super) const DIGEST: usize = DIGEST_LEN; // 4
pub const HALF_DIGEST_LEN: usize = DIGEST / 2; // 2

// `PRECOMPILE_DATA` encoding: see `tables/mod.rs`.
pub const POSEIDON_PRECOMPILE_DATA: usize = 1;
pub const POSEIDON_HALF_OUTPUT_SHIFT: usize = 1 << 1;
pub const POSEIDON_HARDCODED_LEFT_FLAG_SHIFT: usize = 1 << 2;
pub const POSEIDON_HARDCODED_LEFT_OFFSET_SHIFT: usize = 1 << 3;

// ---------- I/O columns ----------
pub const POSEIDON_8_COL_FLAG: ColIndex = 0;
pub const POSEIDON_8_COL_INDEX_INPUT_RIGHT: ColIndex = 1;
pub const POSEIDON_8_COL_INDEX_INPUT_RES: ColIndex = 2;
pub const POSEIDON_8_COL_FLAG_HALF_OUTPUT: ColIndex = 3;
pub const POSEIDON_8_COL_FLAG_HARDCODED_LEFT: ColIndex = 4;
pub const POSEIDON_8_COL_OFFSET_LEFT_HARDCODED: ColIndex = 5;
pub const POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST: ColIndex = 6;
pub const POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND: ColIndex = 7;
pub const POSEIDON_8_COL_INPUT_START: ColIndex = 8;
pub const POSEIDON_8_COL_OUTPUT_START: ColIndex = POSEIDON_8_COL_INPUT_START + WIDTH; // 16
pub const POSEIDON_8_COL_ROUND_START: ColIndex = POSEIDON_8_COL_OUTPUT_START + DIGEST; // 20
/// Non-committed columns ("virtual"):
pub const POSEIDON_8_COL_INDEX_INPUT_LEFT: ColIndex = num_cols_poseidon_8();
pub const POSEIDON_8_COL_PRECOMPILE_DATA: ColIndex = num_cols_poseidon_8() + 1;

pub const POSEIDON8_NAME: &str = "poseidon8_compress";
pub const POSEIDON8_HALF_NAME: &str = "poseidon8_compress_half";
pub const POSEIDON8_HARDCODED_LEFT_NAME: &str = "poseidon8_compress_hardcoded_left";
pub const POSEIDON8_HALF_HARDCODED_LEFT_NAME: &str = "poseidon8_compress_half_hardcoded_left";
pub const ALL_POSEIDON8_NAMES: [&str; 4] = [
    POSEIDON8_NAME,
    POSEIDON8_HALF_NAME,
    POSEIDON8_HARDCODED_LEFT_NAME,
    POSEIDON8_HALF_HARDCODED_LEFT_NAME,
];

// ---------- Per-round aux columns ----------
//
// Goldilocks Poseidon1-8 with the Appendix B sparse partial-round decomposition
// (see `sparse.rs`). The S-box is `x → x⁷` emitted directly as a degree-7
// expression `x·x²·x⁴`, so we commit only the minimum needed to reset degree
// between rounds — no `committed_x3` intermediates.
//
// Per full round: 8 `post[i]` cols (state after MDS).
// Per partial round: 1 `post_sbox` col (the x⁷ output for lane 0); lanes 1..W
// are expressed symbolically as rank-1 updates via `cheap_matmul`.
//
// Constraints:
// - Full round: `post[i] - Σ_j MDS[i][j] · x[j]⁷ = 0`  (deg 7 equality).
// - Partial round: `post_sbox - x⁷ = 0`               (deg 7 equality).
// - Davies-Meyer: `outputs[i] - final_state[i] - inputs[i] = 0`  (deg 1).

const FULL_ROUND_COLS: usize = WIDTH; // 8 post-state
const PARTIAL_ROUND_COLS: usize = 1; // post_sbox

pub const fn is_full_round(r: usize) -> bool {
    r < POSEIDON1_HALF_FULL_ROUNDS || r >= POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS
}

/// First column index of round `r`'s data.
pub const fn round_data_offset(r: usize) -> usize {
    let mut off = POSEIDON_8_COL_ROUND_START;
    let mut i = 0;
    while i < r {
        off += if is_full_round(i) {
            FULL_ROUND_COLS
        } else {
            PARTIAL_ROUND_COLS
        };
        i += 1;
    }
    off
}

pub const fn num_cols_poseidon_8() -> usize {
    round_data_offset(POSEIDON1_N_ROUNDS)
}

pub const fn num_cols_total_poseidon_8() -> usize {
    // +2 for non-committed columns: POSEIDON_8_COL_INDEX_INPUT_LEFT, POSEIDON_8_COL_PRECOMPILE_DATA
    num_cols_poseidon_8() + 2
}

const AUX_COLS_PER_ROW: usize = num_cols_poseidon_8() - POSEIDON_8_COL_ROUND_START;

// ---------- Witness computation ----------
//
// Replay the Poseidon1-8 permutation on `input`, emitting every committed
// column value in trace order. The partial phase uses the sparse
// decomposition so only 2 cols/round are emitted.

fn mds_vec_mul(state: &[F; WIDTH]) -> [F; WIDTH] {
    let mut out = [F::ZERO; WIDTH];
    for i in 0..WIDTH {
        let mut acc = state[0] * F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
        for j in 1..WIDTH {
            acc += state[j] * F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
        }
        out[i] = acc;
    }
    out
}

fn sbox7(x: F) -> F {
    let x2 = x * x;
    let x4 = x2 * x2;
    x4 * x2 * x
}

pub(crate) fn compute_poseidon8_witness(input: [F; WIDTH]) -> (Vec<F>, [F; DIGEST]) {
    let c = get_partial_constants();
    let mut state = input;
    let mut aux = Vec::with_capacity(AUX_COLS_PER_ROW);

    // Initial full rounds.
    for rc in GOLDILOCKS_POSEIDON1_RC_8.iter().take(POSEIDON1_HALF_FULL_ROUNDS) {
        for (i, s) in state.iter_mut().enumerate() {
            *s = sbox7(*s + rc[i]);
        }
        let post = mds_vec_mul(&state);
        for v in &post {
            aux.push(*v);
        }
        state = post;
    }

    // Partial phase: absorb first_round_constants, apply m_i, then sparse rounds.
    for (i, s) in state.iter_mut().enumerate() {
        *s += c.first_round_constants[i];
    }
    {
        let mut after = [F::ZERO; WIDTH];
        for (i, dst) in after.iter_mut().enumerate() {
            let mut acc = F::ZERO;
            for (j, sj) in state.iter().enumerate() {
                acc += c.m_i[i][j] * *sj;
            }
            *dst = acc;
        }
        state = after;
    }

    for r in 0..SPARSE_PARTIAL_ROUNDS {
        let post_sbox = sbox7(state[0]);
        aux.push(post_sbox);

        state[0] = if r < SPARSE_PARTIAL_ROUNDS - 1 {
            post_sbox + c.round_constants[r]
        } else {
            post_sbox
        };

        // cheap_matmul:
        //   new_state[0] = Σ_j sparse_first_row[r][j] · state[j]
        //   new_state[i] = state[i] + v[r][i-1] · old_state[0]    (for i ≥ 1)
        let old_s0 = state[0];
        let mut new_s0 = F::ZERO;
        for (j, sj) in state.iter().enumerate() {
            new_s0 += c.sparse_first_row[r][j] * *sj;
        }
        state[0] = new_s0;
        for (i, s) in state.iter_mut().enumerate().skip(1) {
            *s += c.v[r][i - 1] * old_s0;
        }
    }

    // Terminal full rounds.
    for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
        let abs = POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS + round;
        for i in 0..WIDTH {
            state[i] = sbox7(state[i] + GOLDILOCKS_POSEIDON1_RC_8[abs][i]);
        }
        let post = mds_vec_mul(&state);
        for v in &post {
            aux.push(*v);
        }
        state = post;
    }

    // Davies-Meyer feed-forward.
    let output: [F; DIGEST] = std::array::from_fn(|i| state[i] + input[i]);
    debug_assert_eq!(aux.len(), AUX_COLS_PER_ROW);
    (aux, output)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon8Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon8Precompile<BUS> {
    fn name(&self) -> &'static str {
        POSEIDON8_NAME
    }

    fn table(&self) -> Table {
        Table::poseidon8()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST,
                values: (POSEIDON_8_COL_INPUT_START..POSEIDON_8_COL_INPUT_START + HALF_DIGEST_LEN).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND,
                values: (POSEIDON_8_COL_INPUT_START + HALF_DIGEST_LEN..POSEIDON_8_COL_INPUT_START + DIGEST).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_RIGHT,
                values: (POSEIDON_8_COL_INPUT_START + DIGEST..POSEIDON_8_COL_INPUT_START + DIGEST * 2).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_RES,
                values: (POSEIDON_8_COL_OUTPUT_START..POSEIDON_8_COL_OUTPUT_START + DIGEST).collect(),
            },
        ]
    }

    fn n_columns_total(&self) -> usize {
        num_cols_total_poseidon_8()
    }

    #[allow(clippy::vec_init_then_push)]
    fn bus(&self) -> Bus {
        let mut data = Vec::with_capacity(4);
        data.push(BusData::Column(POSEIDON_8_COL_PRECOMPILE_DATA));
        data.push(BusData::Column(POSEIDON_8_COL_INDEX_INPUT_LEFT));
        data.push(BusData::Column(POSEIDON_8_COL_INDEX_INPUT_RIGHT));
        data.push(BusData::Column(POSEIDON_8_COL_INDEX_INPUT_RES));
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_8_COL_FLAG,
            data,
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; num_cols_total_poseidon_8()];
        row[POSEIDON_8_COL_FLAG] = F::ZERO;
        row[POSEIDON_8_COL_INDEX_INPUT_RIGHT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_INDEX_INPUT_RES] = F::from_usize(null_hash_ptr);
        row[POSEIDON_8_COL_FLAG_HALF_OUTPUT] = F::ZERO;
        row[POSEIDON_8_COL_FLAG_HARDCODED_LEFT] = F::ZERO;
        row[POSEIDON_8_COL_OFFSET_LEFT_HARDCODED] = F::ZERO;
        row[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND] = F::from_usize(zero_vec_ptr + HALF_DIGEST_LEN);
        // Inputs stay zero; compute and fill the matching witness + output.
        let (aux, output) = compute_poseidon8_witness([F::ZERO; WIDTH]);
        for (i, v) in output.iter().enumerate() {
            row[POSEIDON_8_COL_OUTPUT_START + i] = *v;
        }
        for (i, v) in aux.iter().enumerate() {
            row[POSEIDON_8_COL_ROUND_START + i] = *v;
        }
        // Non-committed columns
        row[POSEIDON_8_COL_INDEX_INPUT_LEFT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_PRECOMPILE_DATA] = F::from_usize(POSEIDON_PRECOMPILE_DATA);
        // Sanity: Davies-Meyer witness must agree with the direct primitive.
        debug_assert_eq!(output, poseidon8_compress([F::ZERO; WIDTH]));
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Poseidon8 {
            half_output,
            hardcoded_offset_left,
        } = args
        else {
            unreachable!("Poseidon8 table called with non-Poseidon8 args");
        };
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_offset_left.is_some();
        // Convention:
        //   flag_hardcoded = 0: left input = m[arg_a..arg_a+4] (split as [arg_a..+2], [arg_a+2..+4])
        //   flag_hardcoded = 1: left input = m[offset..offset+2] | m[arg_a..arg_a+2]
        //                   (i.e. arg_a now points to a 2-element data digest, and the first 2
        //                    elements come from the hardcoded prefix at `offset`)
        let left_first_addr = hardcoded_offset_left.unwrap_or(arg_a_usize);
        let left_second_addr = if flag_hardcoded {
            arg_a_usize
        } else {
            arg_a_usize + HALF_DIGEST_LEN
        };
        let arg0_first = ctx.memory.get_slice(left_first_addr, HALF_DIGEST_LEN)?;
        let arg0_second = ctx.memory.get_slice(left_second_addr, HALF_DIGEST_LEN)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), DIGEST)?;

        let mut input = [F::ZERO; WIDTH];
        input[..HALF_DIGEST_LEN].copy_from_slice(&arg0_first);
        input[HALF_DIGEST_LEN..DIGEST].copy_from_slice(&arg0_second);
        input[DIGEST..].copy_from_slice(&arg1);

        let (aux, output) = compute_poseidon8_witness(input);

        if half_output {
            ctx.memory
                .set_slice(index_res_a.to_usize(), &output[..HALF_DIGEST_LEN])?;
        } else {
            ctx.memory.set_slice(index_res_a.to_usize(), &output)?;
        }

        let hardcoded_offset_left_val = hardcoded_offset_left.unwrap_or(0);

        trace.columns[POSEIDON_8_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_RIGHT].push(arg_b);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_RES].push(index_res_a);
        trace.columns[POSEIDON_8_COL_FLAG_HALF_OUTPUT].push(if half_output { F::ONE } else { F::ZERO });
        trace.columns[POSEIDON_8_COL_FLAG_HARDCODED_LEFT].push(if flag_hardcoded { F::ONE } else { F::ZERO });
        trace.columns[POSEIDON_8_COL_OFFSET_LEFT_HARDCODED].push(F::from_usize(hardcoded_offset_left_val));
        trace.columns[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST].push(F::from_usize(left_first_addr));
        trace.columns[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND].push(F::from_usize(left_second_addr));
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_INPUT_START + i].push(*value);
        }
        // The first HALF_DIGEST_LEN trace outputs always equal the permutation output.
        // For half_output rows, the last HALF_DIGEST_LEN are filled later from memory in
        // `fill_trace_poseidon_8`'s post-pass (lookup checks against memory, not the perm).
        for (i, value) in output.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_OUTPUT_START + i].push(*value);
        }
        for (i, value) in aux.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_ROUND_START + i].push(*value);
        }
        // Non-committed columns
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_LEFT].push(arg_a);
        let precompile_data = POSEIDON_PRECOMPILE_DATA
            + POSEIDON_HALF_OUTPUT_SHIFT * (half_output as usize)
            + POSEIDON_HARDCODED_LEFT_FLAG_SHIFT * (flag_hardcoded as usize)
            + POSEIDON_HARDCODED_LEFT_OFFSET_SHIFT * hardcoded_offset_left_val;
        trace.columns[POSEIDON_8_COL_PRECOMPILE_DATA].push(F::from_usize(precompile_data));

        Ok(())
    }
}

/// Constraint count, computed once at monomorphisation. Must match the number
/// of `assert_*` / `eval_virtual_column` / `declare_values` calls issued in
/// `eval()` exactly; used by the proving pipeline for pre-allocation.
const fn poseidon8_n_constraints(bus: bool) -> usize {
    // 1 boolean flag.
    // 2 boolean flags (half_output, hardcoded_left).
    // 2 effective_index constraints (linking effective_index_left_first/second to flag_hardcoded).
    // Initial + terminal full rounds: 8 MDS equality gates per round (deg 7).
    // Partial rounds: 1 post_sbox gate per round (deg 7).
    // Davies-Meyer: HALF_DIGEST_LEN unconditional + HALF_DIGEST_LEN gated outputs (deg 1 / 2).
    // + bus (if enabled).
    let full_gates = 2 * POSEIDON1_HALF_FULL_ROUNDS * WIDTH;
    let partial_gates = POSEIDON1_PARTIAL_ROUNDS;
    1 + 2 + 2 + full_gates + partial_gates + DIGEST + bus as usize
}

impl<const BUS: bool> Air for Poseidon8Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        num_cols_poseidon_8()
    }
    fn degree_air(&self) -> usize {
        // S-box is x⁷ → max degree 7. The half_output gating multiplies by (1 - flag_half_output)
        // so output gates are at most 8.
        8
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        poseidon8_n_constraints(BUS)
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let c = get_partial_constants();

        // Phase 1 — snapshot every `up[…]` column read into owned locals so we
        // can then use `builder` mutably without fighting the borrow checker.
        let flag;
        let index_b;
        let index_res;
        let flag_half_output;
        let flag_hardcoded_left;
        let offset_hardcoded_left;
        let effective_index_left_first;
        let effective_index_left_second;
        let inputs: [AB::IF; WIDTH];
        let outputs: [AB::IF; DIGEST];
        // Per full round: `post[0..W]`. Per partial round: `post_sbox`.
        let mut full_posts: Vec<[AB::IF; WIDTH]> = Vec::with_capacity(2 * POSEIDON1_HALF_FULL_ROUNDS);
        let mut partial_post_sboxes: Vec<AB::IF> = Vec::with_capacity(SPARSE_PARTIAL_ROUNDS);
        {
            let up = builder.up();
            flag = up[POSEIDON_8_COL_FLAG];
            index_b = up[POSEIDON_8_COL_INDEX_INPUT_RIGHT];
            index_res = up[POSEIDON_8_COL_INDEX_INPUT_RES];
            flag_half_output = up[POSEIDON_8_COL_FLAG_HALF_OUTPUT];
            flag_hardcoded_left = up[POSEIDON_8_COL_FLAG_HARDCODED_LEFT];
            offset_hardcoded_left = up[POSEIDON_8_COL_OFFSET_LEFT_HARDCODED];
            effective_index_left_first = up[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_FIRST];
            effective_index_left_second = up[POSEIDON_8_COL_EFFECTIVE_INDEX_LEFT_SECOND];
            inputs = std::array::from_fn(|i| up[POSEIDON_8_COL_INPUT_START + i]);
            outputs = std::array::from_fn(|i| up[POSEIDON_8_COL_OUTPUT_START + i]);

            for round in 0..POSEIDON1_N_ROUNDS {
                let off = round_data_offset(round);
                if is_full_round(round) {
                    let post: [AB::IF; WIDTH] = std::array::from_fn(|i| up[off + i]);
                    full_posts.push(post);
                } else {
                    partial_post_sboxes.push(up[off]);
                }
            }
        }

        // Reconstruct precompile_data and index_a (virtual columns) from the committed flags.
        let precompile_data_reconstructed = AB::IF::ONE
            + flag_half_output * AB::F::from_usize(POSEIDON_HALF_OUTPUT_SHIFT)
            + flag_hardcoded_left * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_FLAG_SHIFT)
            + flag_hardcoded_left * offset_hardcoded_left * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_OFFSET_SHIFT);

        // effective_index_left_first = index_a * (1 - flag_hardcoded_left) + offset * flag_hardcoded_left
        //   ⇒ when flag_hardcoded_left = 0: effective_index_left_first = index_a
        //                                  effective_index_left_second = index_a + HALF_DIGEST_LEN
        //   ⇒ when flag_hardcoded_left = 1: effective_index_left_first = offset
        //                                  effective_index_left_second = index_a
        // We define index_a (virtual) via effective_index_left_second:
        //   index_a = effective_index_left_second - (1 - flag_hardcoded_left) * HALF_DIGEST_LEN
        let one_minus_flag_hardcoded_left = AB::IF::ONE - flag_hardcoded_left;
        let index_a = effective_index_left_second - one_minus_flag_hardcoded_left * AB::F::from_usize(HALF_DIGEST_LEN);

        // Phase 2 — bus / declare.
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag,
                &[precompile_data_reconstructed, index_a, index_b, index_res],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[precompile_data_reconstructed, index_a, index_b, index_res]);
        }

        builder.assert_bool(flag);
        builder.assert_bool(flag_half_output);
        builder.assert_bool(flag_hardcoded_left);

        // Constrain effective_index_left_first to match its semantics.
        builder.assert_zero(flag_hardcoded_left * (offset_hardcoded_left - effective_index_left_first));
        builder.assert_zero(one_minus_flag_hardcoded_left * (index_a - effective_index_left_first));

        // Phase 3 — Poseidon1-8 permutation constraints with Davies-Meyer feed-forward.
        let mut state: [AB::IF; WIDTH] = inputs;

        // ---- Initial full rounds ----
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            let sbox_out: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                let x = state[i] + AB::F::from_u64(GOLDILOCKS_POSEIDON1_RC_8[round][i].as_canonical_u64());
                // x⁷ = x · (x²)² · x² — 4 Mul nodes in the symbolic DAG.
                let x2 = x * x;
                let x4 = x2 * x2;
                x4 * x2 * x
            });
            let post = full_posts[round];
            for i in 0..WIDTH {
                let mut acc = sbox_out[0] * AB::F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
                for (j, sj) in sbox_out.iter().enumerate().skip(1) {
                    let coeff = AB::F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
                    acc += *sj * coeff;
                }
                builder.assert_zero(post[i] - acc);
            }
            state = post;
        }

        // ---- Partial phase: first_round_constants, m_i, sparse-matmul loop ----
        for (i, s) in state.iter_mut().enumerate() {
            *s += AB::F::from_u64(c.first_round_constants[i].as_canonical_u64());
        }
        {
            let mut after: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                let mut acc = state[0] * AB::F::from_u64(c.m_i[i][0].as_canonical_u64());
                for (j, sj) in state.iter().enumerate().skip(1) {
                    acc += *sj * AB::F::from_u64(c.m_i[i][j].as_canonical_u64());
                }
                acc
            });
            std::mem::swap(&mut state, &mut after);
        }

        for (r, post_sbox) in partial_post_sboxes.iter().enumerate().take(SPARSE_PARTIAL_ROUNDS) {
            let x = state[0];
            let post_sbox = *post_sbox;

            // post_sbox = x⁷ (deg 7).
            let x2 = x * x;
            let x4 = x2 * x2;
            builder.assert_zero(post_sbox - x4 * x2 * x);

            // state[0] becomes post_sbox (+ scalar RC, except last round).
            state[0] = if r < SPARSE_PARTIAL_ROUNDS - 1 {
                post_sbox + AB::F::from_u64(c.round_constants[r].as_canonical_u64())
            } else {
                post_sbox
            };

            // cheap_matmul.
            let old_s0 = state[0];
            let mut new_s0 = state[0] * AB::F::from_u64(c.sparse_first_row[r][0].as_canonical_u64());
            for (j, sj) in state.iter().enumerate().skip(1) {
                new_s0 += *sj * AB::F::from_u64(c.sparse_first_row[r][j].as_canonical_u64());
            }
            state[0] = new_s0;
            for (i, s) in state.iter_mut().enumerate().skip(1) {
                *s += old_s0 * AB::F::from_u64(c.v[r][i - 1].as_canonical_u64());
            }
        }

        // ---- Terminal full rounds ----
        for round in 0..POSEIDON1_HALF_FULL_ROUNDS {
            let abs = POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS + round;
            let sbox_out: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                let x = state[i] + AB::F::from_u64(GOLDILOCKS_POSEIDON1_RC_8[abs][i].as_canonical_u64());
                let x2 = x * x;
                let x4 = x2 * x2;
                x4 * x2 * x
            });
            let post = full_posts[POSEIDON1_HALF_FULL_ROUNDS + round];
            for i in 0..WIDTH {
                let mut acc = sbox_out[0] * AB::F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
                for (j, sj) in sbox_out.iter().enumerate().skip(1) {
                    let coeff = AB::F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
                    acc += *sj * coeff;
                }
                builder.assert_zero(post[i] - acc);
            }
            state = post;
        }

        // Davies-Meyer: outputs[i] = final_state[i] + inputs[i] for i in 0..DIGEST.
        // First HALF_DIGEST_LEN outputs: always constrained.
        // Last HALF_DIGEST_LEN outputs: only constrained when flag_half_output = 0.
        let one_minus_flag_half_output = AB::IF::ONE - flag_half_output;
        for i in 0..DIGEST {
            if i < HALF_DIGEST_LEN {
                builder.assert_zero(outputs[i] - state[i] - inputs[i]);
            } else {
                builder.assert_zero(one_minus_flag_half_output * (outputs[i] - state[i] - inputs[i]));
            }
        }
    }
}
