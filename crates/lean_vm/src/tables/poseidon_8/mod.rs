use crate::*;
use crate::execution::memory::MemoryAccess;
use backend::*;
use utils::{ToUsize, poseidon8_compress};

mod trace_gen;
pub use trace_gen::fill_trace_poseidon_8;

pub(super) const WIDTH: usize = 8;
pub(super) const DIGEST: usize = DIGEST_LEN; // 4

pub const POSEIDON_PRECOMPILE_DATA: usize = 1; // domain separation: Poseidon8=1, ExtensionOp>=8

// ---------- I/O columns ----------
pub const POSEIDON_8_COL_FLAG: ColIndex = 0;
pub const POSEIDON_8_COL_INDEX_INPUT_LEFT: ColIndex = 1;
pub const POSEIDON_8_COL_INDEX_INPUT_RIGHT: ColIndex = 2;
pub const POSEIDON_8_COL_INDEX_INPUT_RES: ColIndex = 3;
pub const POSEIDON_8_COL_INPUT_START: ColIndex = 4;
pub const POSEIDON_8_COL_OUTPUT_START: ColIndex = POSEIDON_8_COL_INPUT_START + WIDTH; // 12
pub const POSEIDON_8_COL_ROUND_START: ColIndex = POSEIDON_8_COL_OUTPUT_START + DIGEST; // 16

// Legacy aliases used by other tables/compiler code that still refers to the
// KoalaBear-era names. Keeping them as shims keeps the diff small.
pub const POSEIDON_16_COL_FLAG: ColIndex = POSEIDON_8_COL_FLAG;
pub const POSEIDON_16_COL_INDEX_INPUT_LEFT: ColIndex = POSEIDON_8_COL_INDEX_INPUT_LEFT;
pub const POSEIDON_16_COL_INDEX_INPUT_RIGHT: ColIndex = POSEIDON_8_COL_INDEX_INPUT_RIGHT;
pub const POSEIDON_16_COL_INDEX_INPUT_RES: ColIndex = POSEIDON_8_COL_INDEX_INPUT_RES;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = POSEIDON_8_COL_INPUT_START;

pub const POSEIDON8_NAME: &str = "poseidon8_compress";

// ---------- Per-round aux columns ----------
//
// Goldilocks Poseidon1 width-8: 30 rounds, x⁷ S-box, circulant MDS row
// `MDS8_ROW = [7,1,3,8,8,3,4,9]`, Davies-Meyer feed-forward on the first
// `DIGEST` lanes. Full rounds apply the S-box to every lane; partial rounds
// apply it only to lane 0.
//
// For each round we commit:
//   - `committed_x3[i] = (state[i] + RC[r][i])^3` for every S-box lane,
//   - `post[i]` = entire state after MDS multiply.
//
// The S-box output expression `(x^3)^2 * x = x^7` stays at degree 3, so the
// whole constraint system fits under `degree_air = 3`.

const FULL_ROUND_COLS: usize = WIDTH + WIDTH; // 8 S-box + 8 post-state
const PARTIAL_ROUND_COLS: usize = 1 + WIDTH; // 1 S-box + 8 post-state

pub const fn is_full_round(r: usize) -> bool {
    r < POSEIDON1_HALF_FULL_ROUNDS
        || r >= POSEIDON1_HALF_FULL_ROUNDS + POSEIDON1_PARTIAL_ROUNDS
}

/// First column index of round `r`'s data (committed_x3, then post-state).
pub const fn round_data_offset(r: usize) -> usize {
    let mut off = POSEIDON_8_COL_ROUND_START;
    let mut i = 0;
    while i < r {
        off += if is_full_round(i) { FULL_ROUND_COLS } else { PARTIAL_ROUND_COLS };
        i += 1;
    }
    off
}

/// Number of S-box (committed x³) columns in round `r`.
const fn round_sbox_lanes(r: usize) -> usize {
    if is_full_round(r) { WIDTH } else { 1 }
}

/// First column index of round `r`'s committed post-state.
pub const fn round_post_offset(r: usize) -> usize {
    round_data_offset(r) + round_sbox_lanes(r)
}

pub const fn num_cols_poseidon_8() -> usize {
    round_data_offset(POSEIDON1_N_ROUNDS)
}

const AUX_COLS_PER_ROW: usize = num_cols_poseidon_8() - POSEIDON_8_COL_ROUND_START;

// ---------- Witness computation ----------
//
// Replay the Poseidon1-8 permutation on `input`, returning every intermediate
// witness column (in trace order: round 0's committed_x3s, round 0's post,
// round 1's, …) together with the Davies-Meyer `[F; DIGEST]` digest.

fn mds_row_coeff(j: usize, i: usize) -> F {
    // Circulant matrix: `row_i · sbox_out = Σ_j COEFF[(j - i) mod W] * sbox_out[j]`.
    F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64)
}

pub(crate) fn compute_poseidon8_witness(input: [F; WIDTH]) -> (Vec<F>, [F; DIGEST]) {
    let mut state = input;
    let mut aux = Vec::with_capacity(AUX_COLS_PER_ROW);

    for round in 0..POSEIDON1_N_ROUNDS {
        // AddRoundConstants.
        for i in 0..WIDTH {
            state[i] = state[i] + GOLDILOCKS_POSEIDON1_RC_8[round][i];
        }

        // S-box: commit x³ for each active lane, replace state[i] with x⁷.
        let sbox_lanes = round_sbox_lanes(round);
        let mut committed = [F::ZERO; WIDTH];
        for i in 0..sbox_lanes {
            let x3 = state[i].cube();
            committed[i] = x3;
            aux.push(x3);
            state[i] = x3 * x3 * state[i]; // x⁷ = (x³)² · x
        }

        // MDS multiply.
        let mut post = [F::ZERO; WIDTH];
        for i in 0..WIDTH {
            let mut acc = state[0] * mds_row_coeff(0, i);
            for j in 1..WIDTH {
                acc = acc + state[j] * mds_row_coeff(j, i);
            }
            post[i] = acc;
        }
        for i in 0..WIDTH {
            aux.push(post[i]);
        }
        state = post;

        let _ = committed; // silence unused-var if WIDTH changes upstream
    }

    // Davies-Meyer feed-forward: output = final_state + input, truncated.
    let output: [F; DIGEST] = std::array::from_fn(|i| state[i] + input[i]);
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
                index: POSEIDON_8_COL_INDEX_INPUT_LEFT,
                values: (POSEIDON_8_COL_INPUT_START..POSEIDON_8_COL_INPUT_START + DIGEST).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_RIGHT,
                values: (POSEIDON_8_COL_INPUT_START + DIGEST..POSEIDON_8_COL_INPUT_START + DIGEST * 2)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_RES,
                values: (POSEIDON_8_COL_OUTPUT_START..POSEIDON_8_COL_OUTPUT_START + DIGEST).collect(),
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_8_COL_FLAG,
            data: vec![
                BusData::Constant(POSEIDON_PRECOMPILE_DATA),
                BusData::Column(POSEIDON_8_COL_INDEX_INPUT_LEFT),
                BusData::Column(POSEIDON_8_COL_INDEX_INPUT_RIGHT),
                BusData::Column(POSEIDON_8_COL_INDEX_INPUT_RES),
            ],
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; num_cols_poseidon_8()];
        row[POSEIDON_8_COL_FLAG] = F::ZERO;
        row[POSEIDON_8_COL_INDEX_INPUT_LEFT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_INDEX_INPUT_RIGHT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_INDEX_INPUT_RES] = F::from_usize(null_hash_ptr);
        // Inputs stay zero; compute and fill the matching witness + output.
        let (aux, output) = compute_poseidon8_witness([F::ZERO; WIDTH]);
        debug_assert_eq!(aux.len(), AUX_COLS_PER_ROW);
        for (i, v) in output.iter().enumerate() {
            row[POSEIDON_8_COL_OUTPUT_START + i] = *v;
        }
        for (i, v) in aux.iter().enumerate() {
            row[POSEIDON_8_COL_ROUND_START + i] = *v;
        }
        // Sanity: pure-Poseidon compress should agree with the Davies-Meyer witness.
        debug_assert_eq!(output, poseidon8_compress([F::ZERO; WIDTH]));
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        _: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg0 = ctx.memory.get_slice(arg_a.to_usize(), DIGEST)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), DIGEST)?;

        let mut input = [F::ZERO; WIDTH];
        input[..DIGEST].copy_from_slice(&arg0);
        input[DIGEST..].copy_from_slice(&arg1);

        let (aux, output) = compute_poseidon8_witness(input);

        ctx.memory.set_slice(index_res_a.to_usize(), &output)?;

        trace.columns[POSEIDON_8_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_LEFT].push(arg_a);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_RIGHT].push(arg_b);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_RES].push(index_res_a);
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_INPUT_START + i].push(*value);
        }
        for (i, value) in output.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_OUTPUT_START + i].push(*value);
        }
        for (i, value) in aux.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_ROUND_START + i].push(*value);
        }

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon8Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        num_cols_poseidon_8()
    }
    fn degree_air(&self) -> usize {
        3
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        // 1 boolean flag
        // + 326 per-round gates: each full round = 8 S-box + 8 post; each partial = 1 + 8
        // + 4 Davies-Meyer
        // + bus
        let mut n = 1 + 4 + BUS as usize;
        let mut r = 0;
        while r < POSEIDON1_N_ROUNDS {
            n += round_sbox_lanes(r) + WIDTH;
            r += 1;
        }
        n
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        // Phase 1 — snapshot every column read from `up` into owned locals so
        // we can then use `builder` mutably without fighting the borrow checker.
        let flag;
        let index_a;
        let index_b;
        let index_res;
        let inputs: [AB::IF; WIDTH];
        let outputs: [AB::IF; DIGEST];
        let mut sbox_commits: Vec<Vec<AB::IF>> = Vec::with_capacity(POSEIDON1_N_ROUNDS);
        let mut post_states: Vec<[AB::IF; WIDTH]> = Vec::with_capacity(POSEIDON1_N_ROUNDS);
        {
            let up = builder.up();
            flag = up[POSEIDON_8_COL_FLAG];
            index_a = up[POSEIDON_8_COL_INDEX_INPUT_LEFT];
            index_b = up[POSEIDON_8_COL_INDEX_INPUT_RIGHT];
            index_res = up[POSEIDON_8_COL_INDEX_INPUT_RES];
            inputs = std::array::from_fn(|i| up[POSEIDON_8_COL_INPUT_START + i]);
            outputs = std::array::from_fn(|i| up[POSEIDON_8_COL_OUTPUT_START + i]);
            for r in 0..POSEIDON1_N_ROUNDS {
                let data_off = round_data_offset(r);
                let post_off = round_post_offset(r);
                let n_sbox = round_sbox_lanes(r);
                sbox_commits.push((0..n_sbox).map(|i| up[data_off + i]).collect());
                post_states.push(std::array::from_fn(|i| up[post_off + i]));
            }
        }

        // Phase 2 — bus / declare.
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag,
                &[
                    AB::IF::from_usize(POSEIDON_PRECOMPILE_DATA),
                    index_a,
                    index_b,
                    index_res,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[
                AB::IF::from_usize(POSEIDON_PRECOMPILE_DATA),
                index_a,
                index_b,
                index_res,
            ]);
        }

        builder.assert_bool(flag);

        // Phase 3 — Poseidon1-8 permutation constraints with Davies-Meyer feed-forward.
        let mut state: [AB::IF; WIDTH] = inputs;
        for round in 0..POSEIDON1_N_ROUNDS {
            let sbox_lanes = round_sbox_lanes(round);

            // AddRoundConstants: x[i] = state[i] + RC[r][i] (expression, degree 1).
            let x: [AB::IF; WIDTH] = std::array::from_fn(|i| {
                state[i] + AB::F::from_u64(GOLDILOCKS_POSEIDON1_RC_8[round][i].as_canonical_u64())
            });

            // S-box lanes: commit committed_x3 = x³ and compute sbox_out = x⁷.
            let mut sbox_out: [AB::IF; WIDTH] = x;
            for i in 0..sbox_lanes {
                let committed_x3 = sbox_commits[round][i];
                builder.assert_zero(committed_x3 - x[i] * x[i] * x[i]);
                sbox_out[i] = committed_x3 * committed_x3 * x[i];
            }

            // MDS: post[i] = Σ_j MDS[(j-i) mod W] * sbox_out[j].
            let post = post_states[round];
            for i in 0..WIDTH {
                let coeff0 = AB::F::from_u64(MDS8_ROW[(WIDTH - i) % WIDTH] as u64);
                let mut acc = sbox_out[0] * coeff0;
                for j in 1..WIDTH {
                    let coeff = AB::F::from_u64(MDS8_ROW[(j + WIDTH - i) % WIDTH] as u64);
                    acc = acc + sbox_out[j] * coeff;
                }
                builder.assert_zero(post[i] - acc);
            }

            // Reset state to the committed post-state for the next round.
            state = post;
        }

        // Davies-Meyer: outputs[i] = final_state[i] + inputs[i] for i in 0..DIGEST.
        for i in 0..DIGEST {
            builder.assert_zero(outputs[i] - state[i] - inputs[i]);
        }
    }
}
