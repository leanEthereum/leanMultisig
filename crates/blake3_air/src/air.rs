use backend::{Air, AirBuilder, PrimeCharacteristicRing, QuinticExtensionFieldKB};
use itertools::izip;

use crate::columns::{Blake3Cols, Blake3State, FullRound, NUM_BLAKE3_COLS, QuarterRound};
use crate::constants::{BITS_PER_LIMB, IV, permute};
use crate::utils::{add2, add3, pack_bits_le, xor_32_shift};

type EF = QuinticExtensionFieldKB;

/// Blake3 AIR. Assumes the field size is at least 16 bits.
#[derive(Debug)]
pub struct Blake3Air;

impl Blake3Air {
    /// Verify that the quarter round function has been correctly computed.
    fn quarter_round_function<AB: AirBuilder>(&self, builder: &mut AB, trace: &QuarterRound<'_, AB::F>) {
        // Verify a' = a + b + m_{2i} mod 2^32
        let b_0_16 = pack_bits_le(trace.b[..BITS_PER_LIMB].iter().cloned());
        let b_16_32 = pack_bits_le(trace.b[BITS_PER_LIMB..].iter().cloned());

        add3(builder, trace.a_prime, trace.a, &[b_0_16, b_16_32], trace.m_two_i);

        // Verify d' = (a' ^ d) >> 16, equivalently: a' = d ^ (d' << 16)
        xor_32_shift(builder, trace.a_prime, trace.d, trace.d_prime, 16);

        // Verify c' = c + d' mod 2^32
        let d_prime_0_16 = pack_bits_le(trace.d_prime[..BITS_PER_LIMB].iter().cloned());
        let d_prime_16_32 = pack_bits_le(trace.d_prime[BITS_PER_LIMB..].iter().cloned());
        add2(builder, trace.c_prime, trace.c, &[d_prime_0_16, d_prime_16_32]);

        // Verify b' = (c' ^ b) >> 12, equivalently: c' = b ^ (b' << 12)
        xor_32_shift(builder, trace.c_prime, trace.b, trace.b_prime, 12);

        // Verify a'' = a' + b' + m_{2i + 1} mod 2^32
        let b_prime_0_16 = pack_bits_le(trace.b_prime[..BITS_PER_LIMB].iter().cloned());
        let b_prime_16_32 = pack_bits_le(trace.b_prime[BITS_PER_LIMB..].iter().cloned());

        add3(
            builder,
            trace.a_output,
            trace.a_prime,
            &[b_prime_0_16, b_prime_16_32],
            trace.m_two_i_plus_one,
        );

        // Verify d'' = (a'' ^ d') >> 8, equivalently: a'' = d' ^ (d'' << 8)
        xor_32_shift(builder, trace.a_output, trace.d_prime, trace.d_output, 8);

        // Verify c'' = c' + d'' mod 2^32
        let d_output_0_16 = pack_bits_le(trace.d_output[..BITS_PER_LIMB].iter().cloned());
        let d_output_16_32 = pack_bits_le(trace.d_output[BITS_PER_LIMB..].iter().cloned());
        add2(builder, trace.c_output, trace.c_prime, &[d_output_0_16, d_output_16_32]);

        // Verify b'' = (c'' ^ b') >> 7, equivalently: c'' = b' ^ (b'' << 7)
        xor_32_shift(builder, trace.c_output, trace.b_prime, trace.b_output, 7);
    }

    /// Given data for a full round, produce the data corresponding to a
    /// single application of the quarter round function on a column.
    const fn full_round_to_column_quarter_round<'a, T: Clone>(
        &self,
        input: &'a Blake3State<T>,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[T; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T> {
        QuarterRound {
            a: &input.row0[index],
            b: &input.row1[index],
            c: &input.row2[index],
            d: &input.row3[index],

            m_two_i: &m_vector[2 * index],

            a_prime: &round_data.state_prime.row0[index],
            b_prime: &round_data.state_prime.row1[index],
            c_prime: &round_data.state_prime.row2[index],
            d_prime: &round_data.state_prime.row3[index],

            m_two_i_plus_one: &m_vector[2 * index + 1],

            a_output: &round_data.state_middle.row0[index],
            b_output: &round_data.state_middle.row1[index],
            c_output: &round_data.state_middle.row2[index],
            d_output: &round_data.state_middle.row3[index],
        }
    }

    /// Given data for a full round, produce the data corresponding to a
    /// single application of the quarter round function on a diagonal.
    const fn full_round_to_diagonal_quarter_round<'a, T: Clone>(
        &self,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[T; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T> {
        QuarterRound {
            a: &round_data.state_middle.row0[index],
            b: &round_data.state_middle.row1[(index + 1) % 4],
            c: &round_data.state_middle.row2[(index + 2) % 4],
            d: &round_data.state_middle.row3[(index + 3) % 4],

            m_two_i: &m_vector[2 * index + 8],

            a_prime: &round_data.state_middle_prime.row0[index],
            b_prime: &round_data.state_middle_prime.row1[(index + 1) % 4],
            c_prime: &round_data.state_middle_prime.row2[(index + 2) % 4],
            d_prime: &round_data.state_middle_prime.row3[(index + 3) % 4],

            m_two_i_plus_one: &m_vector[2 * index + 9],

            a_output: &round_data.state_output.row0[index],
            b_output: &round_data.state_output.row1[(index + 1) % 4],
            c_output: &round_data.state_output.row2[(index + 2) % 4],
            d_output: &round_data.state_output.row3[(index + 3) % 4],
        }
    }

    /// Verify a full round of the Blake-3 permutation.
    fn verify_round<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        input: &Blake3State<AB::F>,
        round_data: &FullRound<AB::F>,
        m_vector: &[[AB::F; 2]; 16],
    ) {
        // Mix the columns.
        for i in 0..4 {
            let trace = self.full_round_to_column_quarter_round(input, round_data, m_vector, i);
            self.quarter_round_function(builder, &trace);
        }

        // Mix the diagonals.
        for i in 0..4 {
            let trace = self.full_round_to_diagonal_quarter_round(round_data, m_vector, i);
            self.quarter_round_function(builder, &trace);
        }
    }
}

impl Air for Blake3Air {
    type ExtraData = Vec<EF>;

    fn degree_air(&self) -> usize {
        3 // from add3: acc * (acc+C) * (acc+2C)
    }

    fn n_columns_f_air(&self) -> usize {
        NUM_BLAKE3_COLS
    }

    fn n_columns_ef_air(&self) -> usize {
        0
    }

    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![]
    }

    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }

    fn n_constraints(&self) -> usize {
        // Counted from the eval method:
        // - Input booleans: (16 + 4 + 4 + 4) * 32 = 896
        // - initial_row0 packing: 4 * 2 = 8
        // - initial_row2 constants: 4 * 2 = 8
        // - 7 rounds * constraints_per_round
        //   Each round = 8 quarter_rounds.
        //   Each quarter_round:
        //     add3: 2, xor_32_shift: 32+2=34, add2: 2, xor_32_shift: 34,
        //     add3: 2, xor_32_shift: 34, add2: 2, xor_32_shift: 34
        //     = 2+34+2+34+2+34+2+34 = 144
        //   Per round: 8 * 144 = 1152
        //   7 rounds: 7 * 1152 = 8064
        // - final_round_helpers packing: 4 * 2 = 8
        // - final_round_helpers + outputs[0] booleans: (4 + 4) * 32 = 256
        // - outputs[0] xor_32_shift: 4 * 34 = 136
        // - outputs[1] xor: 4 * 32 = 128
        // - outputs[2] xor: 4 * 32 = 128
        // - outputs[3] xor: 4 * 32 = 128
        // Total = 896 + 8 + 8 + 8064 + 8 + 256 + 136 + 128 + 128 + 128 = 9760
        9760
    }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra_data: &Self::ExtraData) {
        let local: Blake3Cols<AB::F> = {
            let up = builder.up_f();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Blake3Cols<AB::F>>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert!(suffix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            unsafe { std::ptr::read(&shorts[0]) }
        };

        let initial_row_3 = [
            local.counter_low.clone(),
            local.counter_hi.clone(),
            local.block_len.clone(),
            local.flags.clone(),
        ];

        // Check that all initialization inputs are boolean.
        local
            .inputs
            .iter()
            .chain(local.chaining_values[0].iter())
            .chain(local.chaining_values[1].iter())
            .chain(initial_row_3.iter())
            .for_each(|elem| {
                for bit in elem {
                    builder.assert_bool(bit.clone());
                }
            });

        // row0 should contain the packing of the first 4 chaining_values.
        for (bits, word) in local.chaining_values[0].iter().zip(local.initial_row0.clone()) {
            let low_16 = pack_bits_le(bits[..BITS_PER_LIMB].iter().cloned());
            let hi_16 = pack_bits_le(bits[BITS_PER_LIMB..].iter().cloned());
            builder.assert_eq(low_16, word[0].clone());
            builder.assert_eq(hi_16, word[1].clone());
        }

        // row2 should contain the first four constants in IV.
        for (row_elem, constant) in local.initial_row2.iter().zip(IV) {
            builder.assert_eq(row_elem[0].clone(), AB::F::from_u16(constant[0]));
            builder.assert_eq(row_elem[1].clone(), AB::F::from_u16(constant[1]));
        }

        let mut m_values: [[AB::F; 2]; 16] = local.inputs.clone().map(|bits| {
            [
                pack_bits_le(bits[..BITS_PER_LIMB].iter().cloned()),
                pack_bits_le(bits[BITS_PER_LIMB..].iter().cloned()),
            ]
        });

        let initial_state = Blake3State {
            row0: local.initial_row0.clone(),
            row1: local.chaining_values[1].clone(),
            row2: local.initial_row2.clone(),
            row3: initial_row_3,
        };

        // Verify 7 rounds.
        self.verify_round(builder, &initial_state, &local.full_rounds[0], &m_values);
        permute(&mut m_values);

        self.verify_round(
            builder,
            &local.full_rounds[0].state_output,
            &local.full_rounds[1],
            &m_values,
        );
        permute(&mut m_values);

        self.verify_round(
            builder,
            &local.full_rounds[1].state_output,
            &local.full_rounds[2],
            &m_values,
        );
        permute(&mut m_values);

        self.verify_round(
            builder,
            &local.full_rounds[2].state_output,
            &local.full_rounds[3],
            &m_values,
        );
        permute(&mut m_values);

        self.verify_round(
            builder,
            &local.full_rounds[3].state_output,
            &local.full_rounds[4],
            &m_values,
        );
        permute(&mut m_values);

        self.verify_round(
            builder,
            &local.full_rounds[4].state_output,
            &local.full_rounds[5],
            &m_values,
        );
        permute(&mut m_values);

        self.verify_round(
            builder,
            &local.full_rounds[5].state_output,
            &local.full_rounds[6],
            &m_values,
        );

        // Verify the final set of xor's.

        // Convert state_output.row2 to bits for the first 4 outputs.
        for (bits, word) in local
            .final_round_helpers
            .iter()
            .zip(local.full_rounds[6].state_output.row2.clone())
        {
            let low_16 = pack_bits_le(bits[..BITS_PER_LIMB].iter().cloned());
            let hi_16 = pack_bits_le(bits[BITS_PER_LIMB..].iter().cloned());
            builder.assert_eq(low_16, word[0].clone());
            builder.assert_eq(hi_16, word[1].clone());
        }

        // Ensure final_round_helpers and outputs[0] are boolean.
        for bits in local.final_round_helpers.iter().chain(local.outputs[0].iter()) {
            for bit in bits {
                builder.assert_bool(bit.clone());
            }
        }

        // outputs[0]: xor state[i] and state[i+8] for i=0..3
        for (out_bits, left_words, right_bits) in izip!(
            local.outputs[0].clone(),
            local.full_rounds[6].state_output.row0.clone(),
            local.final_round_helpers.clone()
        ) {
            xor_32_shift(builder, &left_words, &out_bits, &right_bits, 0);
        }

        // outputs[1]: xor state[i] and state[i+8] for i=4..7
        for (out_bits, left_bits, right_bits) in izip!(
            local.outputs[1].clone(),
            local.full_rounds[6].state_output.row1.clone(),
            local.full_rounds[6].state_output.row3.clone()
        ) {
            for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
                builder.assert_eq(out_bit, left_bit.xor(&right_bit));
            }
        }

        // outputs[2]: xor state[i+8] and chaining_value[i-8] for i=8..11
        for (out_bits, left_bits, right_bits) in izip!(
            local.outputs[2].clone(),
            local.chaining_values[0].clone(),
            local.final_round_helpers.clone()
        ) {
            for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
                builder.assert_eq(out_bit, left_bit.xor(&right_bit));
            }
        }

        // outputs[3]: xor for i=12..15
        for (out_bits, left_bits, right_bits) in izip!(
            local.outputs[3].clone(),
            local.chaining_values[1].clone(),
            local.full_rounds[6].state_output.row3.clone()
        ) {
            for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
                builder.assert_eq(out_bit, left_bit.xor(&right_bit));
            }
        }
    }
}
