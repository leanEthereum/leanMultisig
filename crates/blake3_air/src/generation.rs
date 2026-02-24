use core::array;
use std::borrow::BorrowMut;

use backend::{PrimeCharacteristicRing, PrimeField32};
use rand::{Rng, SeedableRng, rngs::StdRng};
use rayon::prelude::*;

use crate::columns::{Blake3Cols, Blake3State, FullRound, NUM_BLAKE3_COLS};
use crate::constants::{IV, permute};
use crate::utils::u32_to_bits_le;

/// Generate a Blake3 trace with `n_rows` rows (must be a power of two).
/// Returns column-major format: `Vec<Vec<F>>` of size `[NUM_BLAKE3_COLS][n_rows]`.
pub fn generate_blake3_trace<F: PrimeField32>(n_rows: usize) -> Vec<Vec<F>> {
    assert!(n_rows.is_power_of_two());

    let mut rng = StdRng::seed_from_u64(1);
    let inputs: Vec<[u32; 24]> = (0..n_rows).map(|_| rng.random()).collect();

    // Allocate row-major flat buffer.
    let mut flat = F::zero_vec(n_rows * NUM_BLAKE3_COLS);

    // Split into chunks of NUM_BLAKE3_COLS and fill each row.
    flat.par_chunks_mut(NUM_BLAKE3_COLS)
        .zip(inputs)
        .enumerate()
        .for_each(|(counter, (row_slice, input))| {
            let row: &mut Blake3Cols<F> = row_slice.borrow_mut();
            generate_trace_rows_for_perm(row, input, counter, n_rows);
        });

    // Transpose row-major -> column-major.
    let mut columns = vec![vec![F::ZERO; n_rows]; NUM_BLAKE3_COLS];
    for (row_idx, row_chunk) in flat.chunks(NUM_BLAKE3_COLS).enumerate() {
        for (col_idx, val) in row_chunk.iter().enumerate() {
            columns[col_idx][row_idx] = *val;
        }
    }

    columns
}

/// Fill one row of the trace for a single Blake3 hash.
fn generate_trace_rows_for_perm<F: PrimeCharacteristicRing>(
    row: &mut Blake3Cols<F>,
    input: [u32; 24],
    counter: usize,
    block_len: usize,
) {
    row.inputs = array::from_fn(|i| u32_to_bits_le(input[i]));

    row.chaining_values = array::from_fn(|i| array::from_fn(|j| u32_to_bits_le(input[16 + 4 * i + j])));

    row.counter_low = u32_to_bits_le(counter as u32);
    row.counter_hi = u32_to_bits_le(counter.wrapping_shr(32) as u32);
    row.block_len = u32_to_bits_le(block_len as u32);
    row.flags = u32_to_bits_le(0);

    row.initial_row0 = array::from_fn(|i| {
        [
            F::from_u16(input[16 + i] as u16),
            F::from_u16((input[16 + i] >> 16) as u16),
        ]
    });

    row.initial_row2 = array::from_fn(|i| [F::from_u16(IV[i][0]), F::from_u16(IV[i][1])]);

    let mut m_vec: [u32; 16] = array::from_fn(|i| input[i]);
    let mut state = [
        [input[16], input[16 + 1], input[16 + 2], input[16 + 3]],
        [input[16 + 4], input[16 + 5], input[16 + 6], input[16 + 7]],
        [
            (IV[0][0] as u32) + ((IV[0][1] as u32) << 16),
            (IV[1][0] as u32) + ((IV[1][1] as u32) << 16),
            (IV[2][0] as u32) + ((IV[2][1] as u32) << 16),
            (IV[3][0] as u32) + ((IV[3][1] as u32) << 16),
        ],
        [counter as u32, counter.wrapping_shr(32) as u32, block_len as u32, 0],
    ];

    generate_trace_row_for_round(&mut row.full_rounds[0], &mut state, &m_vec);
    permute(&mut m_vec);
    generate_trace_row_for_round(&mut row.full_rounds[1], &mut state, &m_vec);
    permute(&mut m_vec);
    generate_trace_row_for_round(&mut row.full_rounds[2], &mut state, &m_vec);
    permute(&mut m_vec);
    generate_trace_row_for_round(&mut row.full_rounds[3], &mut state, &m_vec);
    permute(&mut m_vec);
    generate_trace_row_for_round(&mut row.full_rounds[4], &mut state, &m_vec);
    permute(&mut m_vec);
    generate_trace_row_for_round(&mut row.full_rounds[5], &mut state, &m_vec);
    permute(&mut m_vec);
    generate_trace_row_for_round(&mut row.full_rounds[6], &mut state, &m_vec);

    row.final_round_helpers = array::from_fn(|i| u32_to_bits_le(state[2][i]));

    row.outputs[0] = array::from_fn(|i| u32_to_bits_le(state[0][i] ^ state[2][i]));
    row.outputs[1] = array::from_fn(|i| u32_to_bits_le(state[1][i] ^ state[3][i]));
    row.outputs[2] = array::from_fn(|i| u32_to_bits_le(state[2][i] ^ input[16 + i]));
    row.outputs[3] = array::from_fn(|i| u32_to_bits_le(state[3][i] ^ input[20 + i]));
}

fn generate_trace_row_for_round<F: PrimeCharacteristicRing>(
    round_data: &mut FullRound<F>,
    state: &mut [[u32; 4]; 4],
    m_vec: &[u32; 16],
) {
    // First half of column quarter round functions.
    (0..4).for_each(|i| {
        (state[0][i], state[1][i], state[2][i], state[3][i]) =
            verifiable_half_round(state[0][i], state[1][i], state[2][i], state[3][i], m_vec[2 * i], false);
    });
    save_state_to_trace(&mut round_data.state_prime, state);

    // Second half of column quarter round functions.
    (0..4).for_each(|i| {
        (state[0][i], state[1][i], state[2][i], state[3][i]) = verifiable_half_round(
            state[0][i],
            state[1][i],
            state[2][i],
            state[3][i],
            m_vec[2 * i + 1],
            true,
        );
    });
    save_state_to_trace(&mut round_data.state_middle, state);

    // First half of diagonal quarter round functions.
    (0..4).for_each(|i| {
        (
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
        ) = verifiable_half_round(
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
            m_vec[8 + 2 * i],
            false,
        );
    });
    save_state_to_trace(&mut round_data.state_middle_prime, state);

    // Second half of diagonal quarter round functions.
    (0..4).for_each(|i| {
        (
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
        ) = verifiable_half_round(
            state[0][i],
            state[1][(i + 1) % 4],
            state[2][(i + 2) % 4],
            state[3][(i + 3) % 4],
            m_vec[9 + 2 * i],
            true,
        );
    });
    save_state_to_trace(&mut round_data.state_output, state);
}

const fn verifiable_half_round(
    mut a: u32,
    mut b: u32,
    mut c: u32,
    mut d: u32,
    m: u32,
    flag: bool,
) -> (u32, u32, u32, u32) {
    let (rot_1, rot_2) = if flag { (8, 7) } else { (16, 12) };

    a = a.wrapping_add(b);
    a = a.wrapping_add(m);
    d = (d ^ a).rotate_right(rot_1);
    c = c.wrapping_add(d);
    b = (b ^ c).rotate_right(rot_2);

    (a, b, c, d)
}

fn save_state_to_trace<R: PrimeCharacteristicRing>(trace: &mut Blake3State<R>, state: &[[u32; 4]; 4]) {
    trace.row0 = array::from_fn(|i| [R::from_u16(state[0][i] as u16), R::from_u16((state[0][i] >> 16) as u16)]);
    trace.row1 = array::from_fn(|i| u32_to_bits_le(state[1][i]));
    trace.row2 = array::from_fn(|i| [R::from_u16(state[2][i] as u16), R::from_u16((state[2][i] >> 16) as u16)]);
    trace.row3 = array::from_fn(|i| u32_to_bits_le(state[3][i]));
}
