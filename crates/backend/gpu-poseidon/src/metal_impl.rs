// Metal compute backend for Poseidon1-16 leaf hashing on Apple GPUs.

use std::fmt::Write as _;
use std::sync::OnceLock;

use koala_bear::{
    KoalaBear, poseidon1_final_constants, poseidon1_initial_constants, poseidon1_lambda_over_16,
    poseidon1_sparse_first_round_constants, poseidon1_sparse_first_row, poseidon1_sparse_m_i,
    poseidon1_sparse_scalar_round_constants, poseidon1_sparse_v,
};
use metal::{CommandQueue, CompileOptions, ComputePipelineState, Device, MTLResourceOptions, MTLSize, NSUInteger};

pub fn metal_available() -> bool {
    Device::system_default().is_some()
}

// =========================================================================
// Constants generation — embed all Poseidon1-16 round constants and sparse
// decomposition tables into the MSL source string. KoalaBear values are kept
// in Montgomery form so the kernel can use them directly without conversion.
// =========================================================================

fn kb_to_monty_u32(k: KoalaBear) -> u32 {
    // SAFETY: KoalaBear = MontyField31<KoalaBearParameters> is #[repr(transparent)]
    // over a `u32` (the inner `value` field) plus a zero-sized PhantomData.
    // Transmuting therefore yields the Montgomery-form u32.
    unsafe { std::mem::transmute::<KoalaBear, u32>(k) }
}

fn emit_u32_array<const N: usize>(out: &mut String, name: &str, vals: [u32; N]) {
    write!(out, "constant uint {name}[{N}] = {{").unwrap();
    for (i, v) in vals.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        write!(out, "{v}u").unwrap();
    }
    out.push_str("};\n");
}

fn emit_dense_16x16(out: &mut String, name: &str, m: &[[KoalaBear; 16]; 16]) {
    let mut flat = [0u32; 256];
    for i in 0..16 {
        for j in 0..16 {
            flat[i * 16 + j] = kb_to_monty_u32(m[i][j]);
        }
    }
    emit_u32_array(out, name, flat);
}

fn emit_rows(out: &mut String, name: &str, rows: &[[KoalaBear; 16]]) {
    let rows_len = rows.len();
    write!(out, "constant uint {name}[{}] = {{", rows_len * 16).unwrap();
    let mut first = true;
    for row in rows {
        for v in row {
            if !first {
                out.push(',');
            }
            first = false;
            write!(out, "{}u", kb_to_monty_u32(*v)).unwrap();
        }
    }
    out.push_str("};\n");
}

fn generate_msl_source() -> String {
    let mut s = String::new();
    s.push_str("#include <metal_stdlib>\nusing namespace metal;\n\n");
    s.push_str("constant uint PRIME = 0x7f000001u;\n");
    s.push_str("constant uint MONTY_MU = 0x81000001u;\n\n");

    // 16-point FFT twiddles W1..W7 (Montgomery form).
    // Match the values in koala_bear::poseidon1_koalabear_16.
    const TWIDDLES: [u32; 7] = [
        0x08dbd69c, 0x6832fe4a, 0x27ae21e2, 0x7e010002, 0x3a89a025, 0x174e3650, 0x27dfce22,
    ];
    for (i, t) in TWIDDLES.iter().enumerate() {
        let monty = kb_to_monty_u32(KoalaBear::new(*t));
        writeln!(s, "constant uint W{} = {}u;", i + 1, monty).unwrap();
    }

    // FFT MDS eigenvalues / 16.
    let lambda = poseidon1_lambda_over_16();
    let lambda_arr: [u32; 16] = core::array::from_fn(|i| kb_to_monty_u32(lambda[i]));
    emit_u32_array(&mut s, "LAMBDA", lambda_arr);

    // Initial / terminal round constants (4 rounds each).
    let init_rc = poseidon1_initial_constants();
    let term_rc = poseidon1_final_constants();
    emit_rows(&mut s, "INITIAL_RC", init_rc);
    emit_rows(&mut s, "TERMINAL_RC", term_rc);

    // Sparse partial-round decomposition.
    let m_i = poseidon1_sparse_m_i();
    let first_row = poseidon1_sparse_first_row();
    let v = poseidon1_sparse_v();
    let first_rc = poseidon1_sparse_first_round_constants();
    let scalar_rc = poseidon1_sparse_scalar_round_constants();

    emit_dense_16x16(&mut s, "SPARSE_M_I", m_i);
    emit_rows(&mut s, "SPARSE_FIRST_ROW", first_row);
    emit_rows(&mut s, "SPARSE_V", v);

    let first_rc_arr: [u32; 16] = core::array::from_fn(|i| kb_to_monty_u32(first_rc[i]));
    emit_u32_array(&mut s, "SPARSE_FIRST_RC", first_rc_arr);

    let n_scalar = scalar_rc.len();
    write!(s, "constant uint SPARSE_SCALAR_RC[{n_scalar}] = {{").unwrap();
    for (i, c) in scalar_rc.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{}u", kb_to_monty_u32(*c)).unwrap();
    }
    s.push_str("};\n");

    s.push_str(KERNEL_BODY);
    s
}

const KERNEL_BODY: &str = r#"
inline uint kb_add(uint a, uint b) {
    uint s = a + b;
    return s >= PRIME ? s - PRIME : s;
}

inline uint kb_sub(uint a, uint b) {
    return a >= b ? a - b : a + PRIME - b;
}

// Montgomery reduction without 64-bit arithmetic.
// Given x = (hi << 32) + lo where x = a*b (a, b < P), compute a*b * R^-1 mod P.
//   t        = (lo * MU) mod 2^32
//   u        = t * P (as 64-bit: u_hi = mulhi(t, P), u_lo = t * P)
//   x - u is divisible by 2^32, so we keep only the high half;
//   if x < u (signed sub underflows), correct with + P.
inline uint kb_mul(uint a, uint b) {
    uint lo = a * b;
    uint hi = mulhi(a, b);
    uint t = lo * MONTY_MU;
    uint u_lo = t * PRIME;
    uint u_hi = mulhi(t, PRIME);
    bool borrow1 = lo < u_lo;
    // x_hi - u_hi - borrow1, with final borrow detection.
    uint sub = hi - u_hi - (borrow1 ? 1u : 0u);
    bool borrow2 = (hi < u_hi) || (hi == u_hi && borrow1);
    return borrow2 ? sub + PRIME : sub;
}

inline uint cube(uint x) {
    return kb_mul(kb_mul(x, x), x);
}

// Pairwise tree-reduced dot product of two 16-element vectors. Critical path
// is log2(16) = 4 adds + 1 mul instead of the 16-deep serial chain a naive
// `acc += s[i]*r[i]` loop would produce — important because dot16 is on the
// partial-round critical path (state[0] depends on it before the next cube).
inline uint dot16(thread const uint *s, constant uint *r) {
    uint p0 = kb_add(kb_mul(s[0],  r[0]),  kb_mul(s[1],  r[1]));
    uint p1 = kb_add(kb_mul(s[2],  r[2]),  kb_mul(s[3],  r[3]));
    uint p2 = kb_add(kb_mul(s[4],  r[4]),  kb_mul(s[5],  r[5]));
    uint p3 = kb_add(kb_mul(s[6],  r[6]),  kb_mul(s[7],  r[7]));
    uint p4 = kb_add(kb_mul(s[8],  r[8]),  kb_mul(s[9],  r[9]));
    uint p5 = kb_add(kb_mul(s[10], r[10]), kb_mul(s[11], r[11]));
    uint p6 = kb_add(kb_mul(s[12], r[12]), kb_mul(s[13], r[13]));
    uint p7 = kb_add(kb_mul(s[14], r[14]), kb_mul(s[15], r[15]));
    uint q0 = kb_add(p0, p1);
    uint q1 = kb_add(p2, p3);
    uint q2 = kb_add(p4, p5);
    uint q3 = kb_add(p6, p7);
    return kb_add(kb_add(q0, q1), kb_add(q2, q3));
}

// 16-point radix-2 FFT / IFFT butterflies (Montgomery-form KoalaBear).
//   bt:      a = v[lo], b = v[hi]; v[lo] = a+b; v[hi] = a-b
//   neg_dif: a = v[lo], b = v[hi]; v[lo] = a+b; v[hi] = (b-a)*t
//   dit:     a = v[lo], tb = v[hi]*t; v[lo] = a+tb; v[hi] = a-tb
#define BT(v, lo, hi) { uint _a = v[lo]; uint _b = v[hi]; v[lo] = kb_add(_a, _b); v[hi] = kb_sub(_a, _b); }
#define NEG_DIF(v, lo, hi, t) { uint _a = v[lo]; uint _b = v[hi]; v[lo] = kb_add(_a, _b); v[hi] = kb_mul(kb_sub(_b, _a), t); }
#define DIT(v, lo, hi, t) { uint _a = v[lo]; uint _tb = kb_mul(v[hi], t); v[lo] = kb_add(_a, _tb); v[hi] = kb_sub(_a, _tb); }

inline void dif_ifft_16(thread uint *f) {
    BT(f, 0, 8);
    NEG_DIF(f, 1, 9, W7); NEG_DIF(f, 2, 10, W6); NEG_DIF(f, 3, 11, W5);
    NEG_DIF(f, 4, 12, W4); NEG_DIF(f, 5, 13, W3); NEG_DIF(f, 6, 14, W2);
    NEG_DIF(f, 7, 15, W1);
    BT(f, 0, 4);
    NEG_DIF(f, 1, 5, W6); NEG_DIF(f, 2, 6, W4); NEG_DIF(f, 3, 7, W2);
    BT(f, 8, 12);
    NEG_DIF(f, 9, 13, W6); NEG_DIF(f, 10, 14, W4); NEG_DIF(f, 11, 15, W2);
    BT(f, 0, 2); NEG_DIF(f, 1, 3, W4);
    BT(f, 4, 6); NEG_DIF(f, 5, 7, W4);
    BT(f, 8, 10); NEG_DIF(f, 9, 11, W4);
    BT(f, 12, 14); NEG_DIF(f, 13, 15, W4);
    BT(f, 0, 1); BT(f, 2, 3); BT(f, 4, 5); BT(f, 6, 7);
    BT(f, 8, 9); BT(f, 10, 11); BT(f, 12, 13); BT(f, 14, 15);
}

inline void dit_fft_16(thread uint *f) {
    BT(f, 0, 1); BT(f, 2, 3); BT(f, 4, 5); BT(f, 6, 7);
    BT(f, 8, 9); BT(f, 10, 11); BT(f, 12, 13); BT(f, 14, 15);
    BT(f, 0, 2); DIT(f, 1, 3, W4);
    BT(f, 4, 6); DIT(f, 5, 7, W4);
    BT(f, 8, 10); DIT(f, 9, 11, W4);
    BT(f, 12, 14); DIT(f, 13, 15, W4);
    BT(f, 0, 4); DIT(f, 1, 5, W2); DIT(f, 2, 6, W4); DIT(f, 3, 7, W6);
    BT(f, 8, 12); DIT(f, 9, 13, W2); DIT(f, 10, 14, W4); DIT(f, 11, 15, W6);
    BT(f, 0, 8);
    DIT(f, 1, 9, W1); DIT(f, 2, 10, W2); DIT(f, 3, 11, W3); DIT(f, 4, 12, W4);
    DIT(f, 5, 13, W5); DIT(f, 6, 14, W6); DIT(f, 7, 15, W7);
}

// Circulant MDS multiply via FFT:  C * x = DIT_FFT( (lambda/16) * DIF_IFFT(x) )
inline void mds_mul(thread uint *state) {
    dif_ifft_16(state);
    for (int i = 0; i < 16; i++) state[i] = kb_mul(state[i], LAMBDA[i]);
    dit_fft_16(state);
}

inline void full_round(thread uint *state, constant uint *rc) {
    for (int i = 0; i < 16; i++) {
        state[i] = kb_add(state[i], rc[i]);
        state[i] = cube(state[i]);
    }
    mds_mul(state);
}

inline void permute(thread uint *state) {
    // Force full unrolling so the round-array indices fold to compile-time
    // constants and the compiler can keep round constants in registers instead
    // of reissuing constant-memory loads.
    #pragma clang loop unroll(full)
    for (int r = 0; r < 4; r++) {
        full_round(state, &INITIAL_RC[r * 16]);
    }
    #pragma clang loop unroll(full)
    for (int i = 0; i < 16; i++) {
        state[i] = kb_add(state[i], SPARSE_FIRST_RC[i]);
    }
    uint tmp[16];
    #pragma clang loop unroll(full)
    for (int i = 0; i < 16; i++) {
        tmp[i] = dot16(state, &SPARSE_M_I[i * 16]);
    }
    #pragma clang loop unroll(full)
    for (int i = 0; i < 16; i++) state[i] = tmp[i];

    #pragma clang loop unroll(full)
    for (int r = 0; r < 20; r++) {
        state[0] = cube(state[0]);
        if (r < 19) {
            state[0] = kb_add(state[0], SPARSE_SCALAR_RC[r]);
        }
        uint old_s0 = state[0];
        state[0] = dot16(state, &SPARSE_FIRST_ROW[r * 16]);
        #pragma clang loop unroll(full)
        for (int i = 1; i < 16; i++) {
            state[i] = kb_add(state[i], kb_mul(old_s0, SPARSE_V[r * 16 + (i - 1)]));
        }
    }

    #pragma clang loop unroll(full)
    for (int r = 0; r < 4; r++) {
        full_round(state, &TERMINAL_RC[r * 16]);
    }
}

inline void compress(thread uint *state) {
    uint initial[16];
    for (int i = 0; i < 16; i++) initial[i] = state[i];
    permute(state);
    for (int i = 0; i < 16; i++) state[i] = kb_add(state[i], initial[i]);
}

// Kernel: hash a single Poseidon1 compression (test/parity).
kernel void compress_one(
    device const uint *in_state [[buffer(0)]],
    device uint *out_state [[buffer(1)]],
    uint tid [[thread_position_in_grid]]
) {
    uint state[16];
    for (int i = 0; i < 16; i++) state[i] = in_state[tid * 16 + i];
    compress(state);
    for (int i = 0; i < 16; i++) out_state[tid * 16 + i] = state[i];
}

// Kernel: each thread runs `n_iter` chained compressions on its starting state.
// Used to measure steady-state permutation throughput without paying per-thread
// dispatch overhead.
kernel void compress_chain(
    device const uint *in_state [[buffer(0)]],
    device uint *out_state [[buffer(1)]],
    constant uint &n_iter [[buffer(2)]],
    uint tid [[thread_position_in_grid]]
) {
    uint state[16];
    for (int i = 0; i < 16; i++) state[i] = in_state[tid * 16 + i];
    for (uint k = 0; k < n_iter; k++) {
        compress(state);
    }
    for (int i = 0; i < 16; i++) out_state[tid * 16 + i] = state[i];
}

struct LeafParams {
    uint matrix_width;
    uint effective_base_width;
    uint n_pad;
};

// Kernel: one thread per leaf row.
//   matrix[r * matrix_width + c]  -- KoalaBear in Montgomery form
//   initial_state -- 16 KoalaBear values, the pre-absorbed sponge state
//   digests[r * 8 + i] -- output (first 8 state elements)
kernel void hash_leaves(
    device const uint *matrix [[buffer(0)]],
    device const uint *initial_state [[buffer(1)]],
    device uint *digests [[buffer(2)]],
    constant LeafParams &p [[buffer(3)]],
    uint tid [[thread_position_in_grid]]
) {
    uint state[16];
    for (int i = 0; i < 16; i++) state[i] = initial_state[i];

    uint W = p.effective_base_width;
    uint n_pad = p.n_pad;
    uint total_chunks = (W + n_pad) / 8u;
    device const uint *row = matrix + tid * p.matrix_width;

    for (uint chunk_idx = 0; chunk_idx < total_chunks; chunk_idx++) {
        uint saved[16];
        for (int i = 0; i < 16; i++) saved[i] = state[i];

        for (int j = 0; j < 8; j++) {
            uint k = chunk_idx * 8u + (uint)j;
            uint val;
            if (k < n_pad) {
                val = 0u;
            } else {
                uint col = W - 1u - (k - n_pad);
                val = row[col];
            }
            state[15 - j] = val;
        }
        permute(state);
        for (int i = 0; i < 16; i++) state[i] = kb_add(state[i], saved[i]);
    }

    for (int i = 0; i < 8; i++) digests[tid * 8u + (uint)i] = state[i];
}

// Kernel: compress a parent layer of the Merkle tree.
// in_layer: 2*N digests of 8 elements each.
// out_layer: N digests; out[i] = compress(in[2i], in[2i+1])
kernel void compress_pairs(
    device const uint *in_layer [[buffer(0)]],
    device uint *out_layer [[buffer(1)]],
    uint tid [[thread_position_in_grid]]
) {
    uint state[16];
    // state[0..8]  = in_layer[2*tid]   (left child)
    // state[8..16] = in_layer[2*tid+1] (right child)
    for (int i = 0; i < 16; i++) state[i] = in_layer[tid * 16u + (uint)i];
    compress(state);
    for (int i = 0; i < 8; i++) out_layer[tid * 8u + (uint)i] = state[i];
}

struct LeafParamsNoInit {
    uint matrix_width;  // actual number of stored columns per row
    uint full_width;    // total RTL-stream length (>= 16, multiple of 8)
};

// Kernel: hash leaves *without* a precomputed initial state. Mirrors the CPU
// `first_digest_layer` path:
//   stream = [zeros (full_width - matrix_width), matrix RTL]
//   state  = [0; 16]
//   absorb first 16 elements into the full state (state[0..16]); compress
//   absorb remaining 8-element chunks into state[8..16]; compress
// One thread per leaf row.
kernel void hash_leaves_no_initial(
    device const uint *matrix [[buffer(0)]],
    device uint *digests [[buffer(1)]],
    constant LeafParamsNoInit &p [[buffer(2)]],
    uint tid [[thread_position_in_grid]]
) {
    uint W = p.matrix_width;
    uint full = p.full_width;
    uint n_pad = full - W;
    device const uint *row = matrix + tid * W;

    uint state[16];

    // -- First absorption: 16 elements into the entire state -----------------
    for (int j = 0; j < 16; j++) {
        uint k = (uint)j;
        uint val;
        if (k < n_pad) {
            val = 0u;
        } else {
            uint col = W - 1u - (k - n_pad);
            val = row[col];
        }
        state[15 - j] = val;
    }
    uint saved[16];
    for (int i = 0; i < 16; i++) saved[i] = state[i];
    permute(state);
    for (int i = 0; i < 16; i++) state[i] = kb_add(state[i], saved[i]);

    // -- Remaining absorbs: 8 elements into state[8..16] ---------------------
    uint absorbed = 16u;
    while (absorbed < full) {
        for (int i = 0; i < 16; i++) saved[i] = state[i];
        for (int j = 0; j < 8; j++) {
            uint k = absorbed + (uint)j;
            uint val;
            if (k < n_pad) {
                val = 0u;
            } else {
                uint col = W - 1u - (k - n_pad);
                val = row[col];
            }
            state[15 - j] = val;
        }
        permute(state);
        for (int i = 0; i < 16; i++) state[i] = kb_add(state[i], saved[i]);
        absorbed += 8u;
    }

    for (int i = 0; i < 8; i++) digests[tid * 8u + (uint)i] = state[i];
}

// =========================================================================
// FFT support: prepare-evals reshape + radix-2 in-place butterfly layer.
//
// The CPU runs the equivalent of:
//   output = (0..out_len).into_par_iter().map(|i| {
//       let block_index    = i % dft_n_cols;
//       let offset_in_block = i / dft_n_cols;
//       let src = ((block_index << log_block_size) + offset_in_block) >> log_inv_rate;
//       evals[src]
//   }).collect();
// followed by a Stockham-style in-place radix-2 evals-DFT whose butterfly is:
//   t        = (x_2 - x_1) * twiddle
//   x_1_new  = x_1 + t
//   x_2_new  = x_1 - t
// (twiddle-free at offset 0: returns (x_2, 2*x_1 - x_2)).
// =========================================================================

struct PrepareParams {
    uint dft_n_cols;       // = 1 << log_dft_n_cols (power of two when packing aligns)
    uint log_block_size;
    uint log_inv_rate;
    uint elem_size;        // 1 for KoalaBear, 5 for quintic extension
    uint out_len;          // = dft_n_cols * block_size (in elements, not u32s)
};

// One thread per output element. Each element is `elem_size` u32s (1 for F, 5 for EF).
kernel void prepare_evals(
    device const uint *input  [[buffer(0)]],
    device uint       *output [[buffer(1)]],
    constant PrepareParams &p [[buffer(2)]],
    uint tid [[thread_position_in_grid]]
) {
    if (tid >= p.out_len) return;
    uint block_index    = tid % p.dft_n_cols;
    uint offset_in_block = tid / p.dft_n_cols;
    uint src_index = ((block_index << p.log_block_size) + offset_in_block) >> p.log_inv_rate;
    uint src_off = src_index * p.elem_size;
    uint dst_off = tid * p.elem_size;
    for (uint k = 0; k < p.elem_size; k++) {
        output[dst_off + k] = input[src_off + k];
    }
}

struct FftLayerParams {
    uint log_stride;       // butterfly stride = 1 << log_stride
    uint width;            // batch width (number of u32 cols per FFT-row)
    uint half_height;      // grid extent in pair_idx (for explicit bounds check)
};

struct FftRadix4Params {
    uint log_s;             // small stride = 1 << log_s   (layer L)
    uint width;             // batch width
    uint quarter_height;    // grid extent (height / 4)
};

struct FftRadix8Params {
    uint log_s;             // smallest stride (layer L)
    uint width;
    uint eighth_height;     // grid extent (height / 8)
};

// One thread per (column, pair_idx). tid.x = col, tid.y = pair_idx.
// Layout: matrix[row * width + col], row in 0..height, col in 0..width.
// At this layer, pair_idx = block_idx * stride + i_off where:
//   row_a = block_idx * 2 * stride + i_off
//   row_b = row_a + stride
// Stride is a power of two so block_idx and i_off are extracted by shift/mask.
kernel void fft_evals_layer(
    device uint *matrix          [[buffer(0)]],
    constant uint *twiddles      [[buffer(1)]],  // twiddles[0..stride]; [0] is unused (twiddle-free)
    constant FftLayerParams &p   [[buffer(2)]],
    uint2 tid [[thread_position_in_grid]]
) {
    uint col      = tid.x;
    uint pair_idx = tid.y;
    // Metal's dispatch_threads can launch padded threads beyond the requested
    // grid when the grid isn't a multiple of the threadgroup size, so guard
    // against out-of-range coordinates explicitly.
    if (col >= p.width || pair_idx >= p.half_height) return;

    uint stride   = 1u << p.log_stride;
    uint mask     = stride - 1u;
    uint i_off    = pair_idx & mask;
    uint block_idx = pair_idx >> p.log_stride;

    uint row_a = (block_idx << (p.log_stride + 1u)) + i_off;
    uint row_b = row_a + stride;

    uint idx_a = row_a * p.width + col;
    uint idx_b = row_b * p.width + col;

    uint a = matrix[idx_a];
    uint b = matrix[idx_b];

    if (i_off == 0u) {
        // Twiddle-free: (a, b) -> (b, 2a - b)
        matrix[idx_a] = b;
        matrix[idx_b] = kb_sub(kb_add(a, a), b);
    } else {
        uint tw = twiddles[i_off];
        // t = (b - a) * tw; (a, b) -> (a + t, a - t)
        uint t = kb_mul(kb_sub(b, a), tw);
        matrix[idx_a] = kb_add(a, t);
        matrix[idx_b] = kb_sub(a, t);
    }
}

// Radix-4 evals-DFT step: one thread does TWO butterfly layers (stride s and 2s)
// on 4 elements, halving the device-memory passes vs. running two radix-2 layers.
// The decisive win: each radix-2 layer reads/writes the full matrix (~500 GB/s
// memory bandwidth bound on M4 Max). A radix-4 pass moves the same 4 elements
// in/out only once for two layers' worth of butterfly work, ~2× less I/O.
//
// Element layout within a stride-4s block at base address `block_base`:
//   r0 = block_base + i_off        r2 = block_base + 2s + i_off
//   r1 = block_base + s + i_off    r3 = block_base + 3s + i_off
// where i_off in [0, s).
//
// Layer L (stride s) butterflies:  (r0, r1) and (r2, r3) -- both with twiddle
// `twiddles_s[i_off]`. Layer L+1 (stride 2s) butterflies after layer L:
// (r0', r2') with `twiddles_2s[i_off]` and (r1', r3') with `twiddles_2s[i_off+s]`.
kernel void fft_evals_radix4(
    device uint   *matrix       [[buffer(0)]],
    constant uint *twiddles_s   [[buffer(1)]],   // length = s = 1 << log_s
    constant uint *twiddles_2s  [[buffer(2)]],   // length = 2s
    constant FftRadix4Params &p [[buffer(3)]],
    uint2 tid [[thread_position_in_grid]]
) {
    if (tid.x >= p.width || tid.y >= p.quarter_height) return;
    uint col      = tid.x;
    uint pair_idx = tid.y;        // 0 .. height/4

    uint s         = 1u << p.log_s;
    uint mask_s    = s - 1u;
    uint i_off     = pair_idx & mask_s;
    uint block_idx = pair_idx >> p.log_s;
    uint block_base = block_idx << (p.log_s + 2u);  // base of 4s-block

    uint r0 = block_base + i_off;
    uint r1 = r0 + s;
    uint r2 = r0 + (s << 1u);
    uint r3 = r2 + s;

    uint idx0 = r0 * p.width + col;
    uint idx1 = r1 * p.width + col;
    uint idx2 = r2 * p.width + col;
    uint idx3 = r3 * p.width + col;

    uint e0 = matrix[idx0];
    uint e1 = matrix[idx1];
    uint e2 = matrix[idx2];
    uint e3 = matrix[idx3];

    // --- Layer L: stride s ---  butterflies on (e0,e1) and (e2,e3), shared twiddle.
    uint t01, t23;
    if (i_off == 0u) {
        t01 = kb_sub(e1, e0);
        t23 = kb_sub(e3, e2);
    } else {
        uint tw1 = twiddles_s[i_off];
        t01 = kb_mul(kb_sub(e1, e0), tw1);
        t23 = kb_mul(kb_sub(e3, e2), tw1);
    }
    uint e0p = kb_add(e0, t01);
    uint e1p = kb_sub(e0, t01);
    uint e2p = kb_add(e2, t23);
    uint e3p = kb_sub(e2, t23);

    // --- Layer L+1: stride 2s ---  butterflies on (e0', e2') and (e1', e3').
    // Pair (e0', e2') is at offset i_off in the 2s-block: twiddle = twiddles_2s[i_off].
    uint t02;
    if (i_off == 0u) {
        t02 = kb_sub(e2p, e0p);
    } else {
        uint tw2a = twiddles_2s[i_off];
        t02 = kb_mul(kb_sub(e2p, e0p), tw2a);
    }
    uint e0pp = kb_add(e0p, t02);
    uint e2pp = kb_sub(e0p, t02);

    // Pair (e1', e3') is at offset i_off+s in the 2s-block; this is always > 0
    // (we have s >= 1 here), so it always uses a twiddle.
    uint tw2b = twiddles_2s[i_off + s];
    uint t13  = kb_mul(kb_sub(e3p, e1p), tw2b);
    uint e1pp = kb_add(e1p, t13);
    uint e3pp = kb_sub(e1p, t13);

    matrix[idx0] = e0pp;
    matrix[idx1] = e1pp;
    matrix[idx2] = e2pp;
    matrix[idx3] = e3pp;
}

// Radix-8 evals-DFT step: one thread does THREE butterfly layers (strides
// s, 2s, 4s) on 8 elements at positions {0, s, 2s, ..., 7s} within an 8s block.
// Cuts device-memory traffic in 3 vs. three radix-2 passes — for an h=2^19,
// w=224 FFT this brings 19 passes worth of memory traffic down to 7 passes
// (6 radix-8 + 1 radix-2), which moves us from being memory-bandwidth-bound
// at 19 layers to comfortably below the CPU's multi-layer time.
//
// Twiddle access: each subsequent layer doubles the stride, so layer L uses
// `tw_s[i_off]`, layer L+1 uses `tw_2s[i_off + j*s]` for j in {0, 1}, layer
// L+2 uses `tw_4s[i_off + j*s]` for j in {0, 1, 2, 3}. The twiddle-free
// shortcut only kicks in at `i_off == 0` for the first pair in each layer.
kernel void fft_evals_radix8(
    device uint   *matrix    [[buffer(0)]],
    constant uint *tw_s      [[buffer(1)]],   // length = s
    constant uint *tw_2s     [[buffer(2)]],   // length = 2s
    constant uint *tw_4s     [[buffer(3)]],   // length = 4s
    constant FftRadix8Params &p [[buffer(4)]],
    uint2 tid [[thread_position_in_grid]]
) {
    if (tid.x >= p.width || tid.y >= p.eighth_height) return;
    uint col      = tid.x;
    uint pair_idx = tid.y;

    uint s          = 1u << p.log_s;
    uint i_off      = pair_idx & (s - 1u);
    uint block_idx  = pair_idx >> p.log_s;
    uint block_base = block_idx << (p.log_s + 3u);  // 8 * s

    uint stride_w = p.width;
    uint i0 = (block_base + i_off          ) * stride_w + col;
    uint i1 = (block_base + i_off + 1u * s ) * stride_w + col;
    uint i2 = (block_base + i_off + 2u * s ) * stride_w + col;
    uint i3 = (block_base + i_off + 3u * s ) * stride_w + col;
    uint i4 = (block_base + i_off + 4u * s ) * stride_w + col;
    uint i5 = (block_base + i_off + 5u * s ) * stride_w + col;
    uint i6 = (block_base + i_off + 6u * s ) * stride_w + col;
    uint i7 = (block_base + i_off + 7u * s ) * stride_w + col;

    uint e0 = matrix[i0]; uint e1 = matrix[i1];
    uint e2 = matrix[i2]; uint e3 = matrix[i3];
    uint e4 = matrix[i4]; uint e5 = matrix[i5];
    uint e6 = matrix[i6]; uint e7 = matrix[i7];

    // --- Layer L: stride s, pairs (0,1),(2,3),(4,5),(6,7), shared twiddle tw_s[i_off]
    uint t01, t23, t45, t67;
    if (i_off == 0u) {
        t01 = kb_sub(e1, e0); t23 = kb_sub(e3, e2);
        t45 = kb_sub(e5, e4); t67 = kb_sub(e7, e6);
    } else {
        uint tw = tw_s[i_off];
        t01 = kb_mul(kb_sub(e1, e0), tw);
        t23 = kb_mul(kb_sub(e3, e2), tw);
        t45 = kb_mul(kb_sub(e5, e4), tw);
        t67 = kb_mul(kb_sub(e7, e6), tw);
    }
    uint e0p = kb_add(e0, t01); uint e1p = kb_sub(e0, t01);
    uint e2p = kb_add(e2, t23); uint e3p = kb_sub(e2, t23);
    uint e4p = kb_add(e4, t45); uint e5p = kb_sub(e4, t45);
    uint e6p = kb_add(e6, t67); uint e7p = kb_sub(e6, t67);

    // --- Layer L+1: stride 2s
    // Pairs (0,2),(4,6): twiddle tw_2s[i_off]; pairs (1,3),(5,7): twiddle tw_2s[i_off+s]
    uint t02, t46;
    if (i_off == 0u) {
        t02 = kb_sub(e2p, e0p);
        t46 = kb_sub(e6p, e4p);
    } else {
        uint tw_a = tw_2s[i_off];
        t02 = kb_mul(kb_sub(e2p, e0p), tw_a);
        t46 = kb_mul(kb_sub(e6p, e4p), tw_a);
    }
    {
        uint tw_b = tw_2s[i_off + s];
        uint t13 = kb_mul(kb_sub(e3p, e1p), tw_b);
        uint t57 = kb_mul(kb_sub(e7p, e5p), tw_b);
        uint e0pp = kb_add(e0p, t02); uint e2pp = kb_sub(e0p, t02);
        uint e1pp = kb_add(e1p, t13); uint e3pp = kb_sub(e1p, t13);
        uint e4pp = kb_add(e4p, t46); uint e6pp = kb_sub(e4p, t46);
        uint e5pp = kb_add(e5p, t57); uint e7pp = kb_sub(e5p, t57);

        // --- Layer L+2: stride 4s
        // Pairs (0,4),(1,5),(2,6),(3,7) with tw_4s at offsets i_off, i_off+s, i_off+2s, i_off+3s
        uint t04;
        if (i_off == 0u) {
            t04 = kb_sub(e4pp, e0pp);
        } else {
            uint tw0 = tw_4s[i_off];
            t04 = kb_mul(kb_sub(e4pp, e0pp), tw0);
        }
        uint tw1 = tw_4s[i_off + s];
        uint tw2 = tw_4s[i_off + 2u * s];
        uint tw3 = tw_4s[i_off + 3u * s];
        uint t15 = kb_mul(kb_sub(e5pp, e1pp), tw1);
        uint t26 = kb_mul(kb_sub(e6pp, e2pp), tw2);
        uint t37 = kb_mul(kb_sub(e7pp, e3pp), tw3);

        matrix[i0] = kb_add(e0pp, t04); matrix[i4] = kb_sub(e0pp, t04);
        matrix[i1] = kb_add(e1pp, t15); matrix[i5] = kb_sub(e1pp, t15);
        matrix[i2] = kb_add(e2pp, t26); matrix[i6] = kb_sub(e2pp, t26);
        matrix[i3] = kb_add(e3pp, t37); matrix[i7] = kb_sub(e3pp, t37);
    }
}
"#;

// =========================================================================
// Metal context (lazy global)
// =========================================================================

pub struct MetalCtx {
    pub device: Device,
    pub queue: CommandQueue,
    pub compress_one_pipeline: ComputePipelineState,
    pub compress_chain_pipeline: ComputePipelineState,
    pub compress_pairs_pipeline: ComputePipelineState,
    pub hash_leaves_pipeline: ComputePipelineState,
    pub hash_leaves_no_initial_pipeline: ComputePipelineState,
    pub prepare_evals_pipeline: ComputePipelineState,
    pub fft_evals_layer_pipeline: ComputePipelineState,
    pub fft_evals_radix4_pipeline: ComputePipelineState,
    pub fft_evals_radix8_pipeline: ComputePipelineState,
}

// SAFETY: Metal handles are inherently Send/Sync; the metal-rs crate marks them
// as `!Send` to keep the borrow checker honest, but they are reference-counted
// Objective-C objects that we only mutate via thread-safe `commit` paths.
unsafe impl Send for MetalCtx {}
unsafe impl Sync for MetalCtx {}

static CTX: OnceLock<Option<MetalCtx>> = OnceLock::new();

pub fn ctx() -> Option<&'static MetalCtx> {
    CTX.get_or_init(|| try_init_ctx().ok()).as_ref()
}

fn try_init_ctx() -> Result<MetalCtx, String> {
    let device = Device::system_default().ok_or_else(|| "no Metal device".to_string())?;
    let queue = device.new_command_queue();
    let source = generate_msl_source();
    let options = CompileOptions::new();
    let library = device
        .new_library_with_source(&source, &options)
        .map_err(|e| format!("MSL compile failed: {e}"))?;
    let mk = |name: &str| -> Result<ComputePipelineState, String> {
        let f = library
            .get_function(name, None)
            .map_err(|e| format!("kernel {name} not found: {e}"))?;
        device
            .new_compute_pipeline_state_with_function(&f)
            .map_err(|e| format!("pipeline for {name} failed: {e}"))
    };
    let compress_one_pipeline = mk("compress_one")?;
    let compress_chain_pipeline = mk("compress_chain")?;
    let compress_pairs_pipeline = mk("compress_pairs")?;
    let hash_leaves_pipeline = mk("hash_leaves")?;
    let hash_leaves_no_initial_pipeline = mk("hash_leaves_no_initial")?;
    let prepare_evals_pipeline = mk("prepare_evals")?;
    let fft_evals_layer_pipeline = mk("fft_evals_layer")?;
    let fft_evals_radix4_pipeline = mk("fft_evals_radix4")?;
    let fft_evals_radix8_pipeline = mk("fft_evals_radix8")?;
    Ok(MetalCtx {
        device,
        queue,
        compress_one_pipeline,
        compress_chain_pipeline,
        compress_pairs_pipeline,
        hash_leaves_pipeline,
        hash_leaves_no_initial_pipeline,
        prepare_evals_pipeline,
        fft_evals_layer_pipeline,
        fft_evals_radix4_pipeline,
        fft_evals_radix8_pipeline,
    })
}

// =========================================================================
// Public entry points
// =========================================================================

/// Throughput benchmark: launch `n_threads` GPU threads, each running `n_iter`
/// chained Poseidon1 compressions from a zero starting state.
///
/// Returns the elapsed wall-clock time and the total compression count. The
/// per-thread chain amortizes dispatch/scheduling overhead so this measures
/// steady-state permutation throughput rather than per-launch latency.
pub fn bench_compress_chain(n_threads: usize, n_iter: u32) -> (std::time::Duration, usize) {
    let ctx = ctx().expect("Metal context unavailable");
    let byte_len = (n_threads * 16 * 4) as NSUInteger;

    let zeros = vec![0u32; n_threads * 16];
    let in_buf = ctx.device.new_buffer_with_data(
        zeros.as_ptr() as *const _,
        byte_len,
        MTLResourceOptions::StorageModeShared,
    );
    let out_buf = ctx.device.new_buffer(byte_len, MTLResourceOptions::StorageModeShared);

    let cmd = ctx.queue.new_command_buffer();
    let enc = cmd.new_compute_command_encoder();
    enc.set_compute_pipeline_state(&ctx.compress_chain_pipeline);
    enc.set_buffer(0, Some(&in_buf), 0);
    enc.set_buffer(1, Some(&out_buf), 0);
    enc.set_bytes(
        2,
        std::mem::size_of::<u32>() as NSUInteger,
        (&n_iter as *const u32) as *const _,
    );

    let tg_size = ctx.compress_chain_pipeline.max_total_threads_per_threadgroup();

    let start = std::time::Instant::now();
    enc.dispatch_threads(MTLSize::new(n_threads as NSUInteger, 1, 1), MTLSize::new(tg_size, 1, 1));
    enc.end_encoding();
    cmd.commit();
    cmd.wait_until_completed();
    let elapsed = start.elapsed();

    // Touch the output to prevent dead-code elimination.
    let _ = unsafe { *(out_buf.contents() as *const u32) };

    (elapsed, n_threads * n_iter as usize)
}

/// Run a single Poseidon1 compression on each [u32; 16] state in `inputs`,
/// returning the resulting [u32; 16] states. Used for tests.
pub fn compress_many(inputs: &[[u32; 16]]) -> Vec<[u32; 16]> {
    let ctx = ctx().expect("Metal context unavailable");
    let n = inputs.len();
    let byte_len = (n * 16 * 4) as NSUInteger;

    let in_buf = ctx.device.new_buffer_with_data(
        inputs.as_ptr() as *const _,
        byte_len,
        MTLResourceOptions::StorageModeShared,
    );
    let out_buf = ctx.device.new_buffer(byte_len, MTLResourceOptions::StorageModeShared);

    let cmd = ctx.queue.new_command_buffer();
    let enc = cmd.new_compute_command_encoder();
    enc.set_compute_pipeline_state(&ctx.compress_one_pipeline);
    enc.set_buffer(0, Some(&in_buf), 0);
    enc.set_buffer(1, Some(&out_buf), 0);

    let tg_size = ctx.compress_one_pipeline.max_total_threads_per_threadgroup();
    enc.dispatch_threads(MTLSize::new(n as NSUInteger, 1, 1), MTLSize::new(tg_size, 1, 1));
    enc.end_encoding();
    cmd.commit();
    cmd.wait_until_completed();

    let mut out = vec![[0u32; 16]; n];
    unsafe {
        std::ptr::copy_nonoverlapping(out_buf.contents() as *const u32, out.as_mut_ptr() as *mut u32, n * 16);
    }
    out
}

#[repr(C)]
#[derive(Copy, Clone)]
struct LeafParams {
    matrix_width: u32,
    effective_base_width: u32,
    n_pad: u32,
}

/// Hash each leaf (row) of the matrix using Poseidon1-16 sponge absorption with
/// a precomputed initial state. Returns one [u32; 8] digest per row.
///
/// - `matrix_values`: row-major Montgomery-form u32, length = height * matrix_width.
/// - `matrix_width`: physical row stride (columns actually stored).
/// - `effective_base_width`: only the first `effective_base_width` columns of each
///   row are absorbed; the rest are treated as the zero-suffix already baked into
///   `initial_state`.
/// - `initial_state`: 16 Montgomery-form u32 values — the sponge state after
///   absorbing the trailing zero chunks (see `precompute_zero_suffix_state`).
pub fn hash_leaves_with_initial_state(
    matrix_values: &[u32],
    height: usize,
    matrix_width: usize,
    effective_base_width: usize,
    initial_state: &[u32; 16],
) -> Vec<[u32; 8]> {
    let ctx = ctx().expect("Metal context unavailable");
    assert_eq!(matrix_values.len(), height * matrix_width);

    let n_pad = ((8 - effective_base_width % 8) % 8) as u32;
    let params = LeafParams {
        matrix_width: matrix_width as u32,
        effective_base_width: effective_base_width as u32,
        n_pad,
    };

    let matrix_bytes = (matrix_values.len() * 4) as NSUInteger;
    let digest_bytes = (height * 8 * 4) as NSUInteger;

    // Apple Silicon has unified memory, so a Metal buffer in shared storage mode
    // can wrap an existing CPU pointer with zero copy — provided the pointer is
    // page-aligned and the length is a multiple of the page size. Large Rust Vecs
    // are typically backed by mmap on macOS and ARE page-aligned in practice, so
    // we try the no-copy path first and fall back to the copying `with_data` API
    // only if alignment requirements aren't met.
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let ptr_addr = matrix_values.as_ptr() as usize;
    let no_copy_ok =
        page_size > 0 && ptr_addr.is_multiple_of(page_size) && (matrix_bytes as usize).is_multiple_of(page_size);

    let _upload_span = tracing::info_span!("GPU upload", bytes = matrix_bytes as u64, no_copy = no_copy_ok).entered();
    let matrix_buf = if no_copy_ok {
        // Caller owns the buffer's lifetime; deallocator = None means Metal
        // does NOT free the memory when the Buffer is dropped. We `wait_until_completed`
        // before returning, so the underlying `matrix_values` slice outlives the
        // command buffer's use of it.
        ctx.device.new_buffer_with_bytes_no_copy(
            matrix_values.as_ptr() as *const _,
            matrix_bytes,
            MTLResourceOptions::StorageModeShared,
            None,
        )
    } else {
        ctx.device.new_buffer_with_data(
            matrix_values.as_ptr() as *const _,
            matrix_bytes,
            MTLResourceOptions::StorageModeShared,
        )
    };
    let initial_buf = ctx.device.new_buffer_with_data(
        initial_state.as_ptr() as *const _,
        (16 * 4) as NSUInteger,
        MTLResourceOptions::StorageModeShared,
    );
    let digest_buf = ctx
        .device
        .new_buffer(digest_bytes, MTLResourceOptions::StorageModeShared);
    drop(_upload_span);

    let _dispatch_span = tracing::info_span!("GPU dispatch+wait").entered();
    let cmd = ctx.queue.new_command_buffer();
    let enc = cmd.new_compute_command_encoder();
    enc.set_compute_pipeline_state(&ctx.hash_leaves_pipeline);
    enc.set_buffer(0, Some(&matrix_buf), 0);
    enc.set_buffer(1, Some(&initial_buf), 0);
    enc.set_buffer(2, Some(&digest_buf), 0);
    enc.set_bytes(
        3,
        std::mem::size_of::<LeafParams>() as NSUInteger,
        (&params as *const LeafParams) as *const _,
    );

    let tg_size = ctx.hash_leaves_pipeline.max_total_threads_per_threadgroup();
    enc.dispatch_threads(MTLSize::new(height as NSUInteger, 1, 1), MTLSize::new(tg_size, 1, 1));
    enc.end_encoding();
    cmd.commit();
    cmd.wait_until_completed();
    drop(_dispatch_span);

    let _download_span = tracing::info_span!("GPU download").entered();
    let mut out = vec![[0u32; 8]; height];
    unsafe {
        std::ptr::copy_nonoverlapping(
            digest_buf.contents() as *const u32,
            out.as_mut_ptr() as *mut u32,
            height * 8,
        );
    }
    out
}

/// Hash all leaves AND build all parent Merkle layers entirely on the GPU.
///
/// Returns `digest_layers[k]` of length `height >> k`, with `digest_layers[0]`
/// being the leaf digests and the last entry being the singleton root.
///
/// The parent layers are produced by `compress_pairs` kernel dispatches chained
/// inside one command buffer, so layer-to-layer data stays in shared (GPU-resident)
/// memory and there is no per-layer CPU round-trip.
#[allow(clippy::too_many_arguments)]
pub fn build_merkle_tree_full(
    matrix_values: &[u32],
    height: usize,
    matrix_width: usize,
    effective_base_width: usize,
    initial_state: &[u32; 16],
) -> Vec<Vec<[u32; 8]>> {
    let ctx = ctx().expect("Metal context unavailable");
    assert_eq!(matrix_values.len(), height * matrix_width);
    assert!(
        height.is_power_of_two() || height == 1,
        "height should be a power of two"
    );

    let n_pad = ((8 - effective_base_width % 8) % 8) as u32;
    let params = LeafParams {
        matrix_width: matrix_width as u32,
        effective_base_width: effective_base_width as u32,
        n_pad,
    };

    let matrix_bytes = (matrix_values.len() * 4) as NSUInteger;

    // -- Upload (zero-copy when the source pointer is page-aligned) -----------
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let ptr_addr = matrix_values.as_ptr() as usize;
    let no_copy_ok =
        page_size > 0 && ptr_addr.is_multiple_of(page_size) && (matrix_bytes as usize).is_multiple_of(page_size);

    let _upload_span = tracing::info_span!("GPU upload", bytes = matrix_bytes as u64, no_copy = no_copy_ok).entered();
    let matrix_buf = if no_copy_ok {
        ctx.device.new_buffer_with_bytes_no_copy(
            matrix_values.as_ptr() as *const _,
            matrix_bytes,
            MTLResourceOptions::StorageModeShared,
            None,
        )
    } else {
        ctx.device.new_buffer_with_data(
            matrix_values.as_ptr() as *const _,
            matrix_bytes,
            MTLResourceOptions::StorageModeShared,
        )
    };
    let initial_buf = ctx.device.new_buffer_with_data(
        initial_state.as_ptr() as *const _,
        (16 * 4) as NSUInteger,
        MTLResourceOptions::StorageModeShared,
    );
    drop(_upload_span);

    // -- Allocate one buffer per layer ---------------------------------------
    let mut log_height = 0;
    while (1usize << log_height) < height {
        log_height += 1;
    }
    let n_layers = log_height + 1;
    let mut layer_buffers = Vec::with_capacity(n_layers);
    for k in 0..n_layers {
        let n = height >> k;
        let bytes = (n * 8 * 4) as NSUInteger;
        layer_buffers.push(ctx.device.new_buffer(bytes, MTLResourceOptions::StorageModeShared));
    }

    // -- Encode all dispatches into a single command buffer ------------------
    let _dispatch_span = tracing::info_span!("GPU dispatch+wait (full tree)").entered();
    let cmd = ctx.queue.new_command_buffer();

    {
        let enc = cmd.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&ctx.hash_leaves_pipeline);
        enc.set_buffer(0, Some(&matrix_buf), 0);
        enc.set_buffer(1, Some(&initial_buf), 0);
        enc.set_buffer(2, Some(&layer_buffers[0]), 0);
        enc.set_bytes(
            3,
            std::mem::size_of::<LeafParams>() as NSUInteger,
            (&params as *const LeafParams) as *const _,
        );
        let tg = ctx.hash_leaves_pipeline.max_total_threads_per_threadgroup();
        enc.dispatch_threads(MTLSize::new(height as NSUInteger, 1, 1), MTLSize::new(tg, 1, 1));
        enc.end_encoding();
    }

    for (k, pair) in layer_buffers.windows(2).enumerate() {
        let n = height >> (k + 1);
        let enc = cmd.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&ctx.compress_pairs_pipeline);
        enc.set_buffer(0, Some(&pair[0]), 0);
        enc.set_buffer(1, Some(&pair[1]), 0);
        let tg = ctx
            .compress_pairs_pipeline
            .max_total_threads_per_threadgroup()
            .min(n as NSUInteger);
        enc.dispatch_threads(MTLSize::new(n as NSUInteger, 1, 1), MTLSize::new(tg.max(1), 1, 1));
        enc.end_encoding();
    }

    cmd.commit();
    cmd.wait_until_completed();
    drop(_dispatch_span);

    // -- Download all layers --------------------------------------------------
    let _download_span = tracing::info_span!("GPU download (full tree)").entered();
    let mut layers: Vec<Vec<[u32; 8]>> = Vec::with_capacity(n_layers);
    for (k, buf) in layer_buffers.iter().enumerate() {
        let n = height >> k;
        let mut layer = vec![[0u32; 8]; n];
        unsafe {
            std::ptr::copy_nonoverlapping(buf.contents() as *const u32, layer.as_mut_ptr() as *mut u32, n * 8);
        }
        layers.push(layer);
    }
    layers
}

#[repr(C)]
#[derive(Copy, Clone)]
struct LeafParamsNoInit {
    matrix_width: u32,
    full_width: u32,
}

/// Build the entire Merkle tree on GPU starting from a *zero* sponge state —
/// i.e. when the leaf widths don't admit a precomputed initial state. Used by
/// the WHIR open-rounds where `effective == full` so there is no zero suffix.
///
/// `matrix_width`: physical row stride (columns actually stored per row).
/// `full_width`: total RTL-stream length (must be a multiple of `RATE = 8`,
/// `>= WIDTH = 16`). Any padding at the start of the RTL stream is treated as
/// zeros (which happens when `full_width > matrix_width`).
pub fn build_merkle_tree_full_no_initial(
    matrix_values: &[u32],
    height: usize,
    matrix_width: usize,
    full_width: usize,
) -> Vec<Vec<[u32; 8]>> {
    let ctx = ctx().expect("Metal context unavailable");
    assert_eq!(matrix_values.len(), height * matrix_width);
    assert!(full_width >= 16 && full_width.is_multiple_of(8));
    assert!(
        height.is_power_of_two() || height == 1,
        "height should be a power of two"
    );

    let params = LeafParamsNoInit {
        matrix_width: matrix_width as u32,
        full_width: full_width as u32,
    };

    let matrix_bytes = (matrix_values.len() * 4) as NSUInteger;

    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let ptr_addr = matrix_values.as_ptr() as usize;
    let no_copy_ok =
        page_size > 0 && ptr_addr.is_multiple_of(page_size) && (matrix_bytes as usize).is_multiple_of(page_size);

    let _upload_span = tracing::info_span!("GPU upload", bytes = matrix_bytes as u64, no_copy = no_copy_ok).entered();
    let matrix_buf = if no_copy_ok {
        ctx.device.new_buffer_with_bytes_no_copy(
            matrix_values.as_ptr() as *const _,
            matrix_bytes,
            MTLResourceOptions::StorageModeShared,
            None,
        )
    } else {
        ctx.device.new_buffer_with_data(
            matrix_values.as_ptr() as *const _,
            matrix_bytes,
            MTLResourceOptions::StorageModeShared,
        )
    };
    drop(_upload_span);

    let mut log_height = 0;
    while (1usize << log_height) < height {
        log_height += 1;
    }
    let n_layers = log_height + 1;
    let mut layer_buffers = Vec::with_capacity(n_layers);
    for k in 0..n_layers {
        let n = height >> k;
        let bytes = (n * 8 * 4) as NSUInteger;
        layer_buffers.push(ctx.device.new_buffer(bytes, MTLResourceOptions::StorageModeShared));
    }

    let _dispatch_span = tracing::info_span!("GPU dispatch+wait (full tree, no initial)").entered();
    let cmd = ctx.queue.new_command_buffer();

    {
        let enc = cmd.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&ctx.hash_leaves_no_initial_pipeline);
        enc.set_buffer(0, Some(&matrix_buf), 0);
        enc.set_buffer(1, Some(&layer_buffers[0]), 0);
        enc.set_bytes(
            2,
            std::mem::size_of::<LeafParamsNoInit>() as NSUInteger,
            (&params as *const LeafParamsNoInit) as *const _,
        );
        let tg = ctx
            .hash_leaves_no_initial_pipeline
            .max_total_threads_per_threadgroup()
            .min(64);
        enc.dispatch_threads(MTLSize::new(height as NSUInteger, 1, 1), MTLSize::new(tg, 1, 1));
        enc.end_encoding();
    }

    for (k, pair) in layer_buffers.windows(2).enumerate() {
        let n = height >> (k + 1);
        let enc = cmd.new_compute_command_encoder();
        enc.set_compute_pipeline_state(&ctx.compress_pairs_pipeline);
        enc.set_buffer(0, Some(&pair[0]), 0);
        enc.set_buffer(1, Some(&pair[1]), 0);
        let tg = ctx
            .compress_pairs_pipeline
            .max_total_threads_per_threadgroup()
            .min(n as NSUInteger);
        enc.dispatch_threads(MTLSize::new(n as NSUInteger, 1, 1), MTLSize::new(tg.max(1), 1, 1));
        enc.end_encoding();
    }

    cmd.commit();
    cmd.wait_until_completed();
    drop(_dispatch_span);

    let _download_span = tracing::info_span!("GPU download (full tree, no initial)").entered();
    let mut layers: Vec<Vec<[u32; 8]>> = Vec::with_capacity(n_layers);
    for (k, buf) in layer_buffers.iter().enumerate() {
        let n = height >> k;
        let mut layer = vec![[0u32; 8]; n];
        unsafe {
            std::ptr::copy_nonoverlapping(buf.contents() as *const u32, layer.as_mut_ptr() as *mut u32, n * 8);
        }
        layers.push(layer);
    }
    layers
}

// =========================================================================
// FFT GPU dispatch
// =========================================================================

#[repr(C)]
#[derive(Copy, Clone)]
struct PrepareParams {
    dft_n_cols: u32,
    log_block_size: u32,
    log_inv_rate: u32,
    elem_size: u32,
    out_len: u32,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FftLayerParams {
    log_stride: u32,
    width: u32,
    half_height: u32,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FftRadix4Params {
    log_s: u32,
    width: u32,
    quarter_height: u32,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FftRadix8Params {
    log_s: u32,
    width: u32,
    eighth_height: u32,
}

/// Wrap a `&[u32]` as a Metal buffer with zero copy when page-aligned, else
/// fall back to the copying `with_data` constructor. The second return value
/// is `true` when the buffer aliases the input — i.e. kernel writes to it
/// will land back in the original slice with no readback step needed.
fn buf_from_slice(ctx: &MetalCtx, data: &[u32]) -> (metal::Buffer, bool) {
    let bytes = (data.len() * 4) as NSUInteger;
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as usize;
    let ptr_addr = data.as_ptr() as usize;
    let no_copy = page_size > 0 && ptr_addr.is_multiple_of(page_size) && (bytes as usize).is_multiple_of(page_size);
    let buf = if no_copy {
        ctx.device.new_buffer_with_bytes_no_copy(
            data.as_ptr() as *const _,
            bytes,
            MTLResourceOptions::StorageModeShared,
            None,
        )
    } else {
        ctx.device
            .new_buffer_with_data(data.as_ptr() as *const _, bytes, MTLResourceOptions::StorageModeShared)
    };
    (buf, no_copy)
}

/// Reshape `evals` for the batched FFT, mirroring `prepare_evals_for_fft_unpacked`.
///
/// `evals_u32` is the input slice (length = `evals_count * elem_size`).
/// `out_u32` is the output slice (length = `out_count * elem_size`) — must be
/// pre-allocated. `elem_size` is 1 for `KoalaBear` and 5 for the quintic
/// extension; the kernel copies that many u32s per logical element.
pub fn prepare_evals_for_fft_gpu(
    evals_u32: &[u32],
    out_u32: &mut [u32],
    dft_n_cols: usize,
    log_block_size: usize,
    log_inv_rate: usize,
    elem_size: usize,
) {
    let ctx = ctx().expect("Metal context unavailable");
    let out_len = out_u32.len() / elem_size;
    assert_eq!(
        out_len * elem_size,
        out_u32.len(),
        "out length must be a multiple of elem_size"
    );

    let params = PrepareParams {
        dft_n_cols: dft_n_cols as u32,
        log_block_size: log_block_size as u32,
        log_inv_rate: log_inv_rate as u32,
        elem_size: elem_size as u32,
        out_len: out_len as u32,
    };

    let (in_buf, _) = buf_from_slice(ctx, evals_u32);
    let (out_buf, out_no_copy) = buf_from_slice(ctx, out_u32);

    let cmd = ctx.queue.new_command_buffer();
    let enc = cmd.new_compute_command_encoder();
    enc.set_compute_pipeline_state(&ctx.prepare_evals_pipeline);
    enc.set_buffer(0, Some(&in_buf), 0);
    enc.set_buffer(1, Some(&out_buf), 0);
    enc.set_bytes(
        2,
        std::mem::size_of::<PrepareParams>() as NSUInteger,
        (&params as *const PrepareParams) as *const _,
    );
    let tg = ctx.prepare_evals_pipeline.max_total_threads_per_threadgroup();
    enc.dispatch_threads(
        MTLSize::new(out_len as NSUInteger, 1, 1),
        MTLSize::new(tg.min(out_len as NSUInteger).max(1), 1, 1),
    );
    enc.end_encoding();
    cmd.commit();
    cmd.wait_until_completed();

    if !out_no_copy {
        // The output buffer is a fresh allocation; copy its contents back.
        unsafe {
            std::ptr::copy_nonoverlapping(out_buf.contents() as *const u32, out_u32.as_mut_ptr(), out_u32.len());
        }
    }
}

/// In-place radix-2 evals-DFT on a base-field matrix laid out row-major as
/// `Vec<u32>`. `height` must be a power of two; `width` is the batch dimension
/// (number of independent FFTs run in parallel, one per column).
///
/// `twiddles[layer]` (length `2^layer`) holds the layer's twiddles in Montgomery
/// form. Borrowed as `&[&[u32]]` to avoid per-call cloning of the cached table.
///
/// The data must already be page-aligned so the kernel can write back without
/// a memcpy (this is the case for buffers allocated through `zk-alloc`).
pub fn fft_evals_in_place_gpu(matrix: &mut [u32], height: usize, width: usize, twiddles: &[&[u32]]) {
    let ctx = ctx().expect("Metal context unavailable");
    assert_eq!(matrix.len(), height * width);
    assert!(height.is_power_of_two() && height >= 2);
    let log_h = height.trailing_zeros() as usize;
    assert_eq!(twiddles.len(), log_h, "need one twiddle table per layer");

    let (matrix_buf, matrix_no_copy) = buf_from_slice(ctx, matrix);

    // Upload all twiddle layers once, indexed by layer.
    let twiddle_bufs: Vec<metal::Buffer> = twiddles.iter().map(|t| buf_from_slice(ctx, t).0).collect();

    let cmd = ctx.queue.new_command_buffer();

    // Run layers in radix-4 pairs when possible (one kernel pass per pair of
    // consecutive layers), falling back to radix-2 for the leftover layer
    // when `log_h` is odd. Radix-4 cuts device-memory traffic in half — each
    // group of 4 elements is read once and written once for two layers' worth
    // of butterfly work — which is decisive on memory-bandwidth-bound FFTs.
    //
    // All passes share one compute encoder with a `memory_barrier_with_resources`
    // between them. Splitting layers across encoders adds ~2 ms of pipeline
    // stall per boundary on Apple GPU, which dwarfs the actual butterfly time.
    let w = width as NSUInteger;
    let max_tg = ctx.fft_evals_layer_pipeline.max_total_threads_per_threadgroup();
    let matrix_resources: [&metal::ResourceRef; 1] = [&matrix_buf];

    let enc = cmd.new_compute_command_encoder();
    enc.set_buffer(0, Some(&matrix_buf), 0);

    let mut layer = 0;
    let mut pass = 0;
    while layer < log_h {
        let remaining = log_h - layer;
        if pass > 0 {
            enc.memory_barrier_with_resources(&matrix_resources);
        }
        if remaining >= 3 {
            // Radix-8: process 3 consecutive layers in one pass.
            enc.set_compute_pipeline_state(&ctx.fft_evals_radix8_pipeline);
            let log_s = layer;
            let tw_s_idx = log_h - 1 - layer;
            let tw_2s_idx = log_h - 1 - (layer + 1);
            let tw_4s_idx = log_h - 1 - (layer + 2);
            let eighth_h = (height / 8) as NSUInteger;
            let params = FftRadix8Params {
                log_s: log_s as u32,
                width: width as u32,
                eighth_height: eighth_h as u32,
            };
            enc.set_buffer(1, Some(&twiddle_bufs[tw_s_idx]), 0);
            enc.set_buffer(2, Some(&twiddle_bufs[tw_2s_idx]), 0);
            enc.set_buffer(3, Some(&twiddle_bufs[tw_4s_idx]), 0);
            enc.set_bytes(
                4,
                std::mem::size_of::<FftRadix8Params>() as NSUInteger,
                (&params as *const FftRadix8Params) as *const _,
            );
            let tg_x = w.min(max_tg).max(1);
            let tg_y = ((max_tg / tg_x).max(1)).min(eighth_h);
            enc.dispatch_threads(MTLSize::new(w, eighth_h, 1), MTLSize::new(tg_x, tg_y, 1));
            layer += 3;
        } else if remaining == 2 {
            // Radix-4: 2 consecutive layers in one pass.
            enc.set_compute_pipeline_state(&ctx.fft_evals_radix4_pipeline);
            let log_s = layer;
            let tw_s_idx = log_h - 1 - layer;
            let tw_2s_idx = log_h - 1 - (layer + 1);
            let quarter_h = (height / 4) as NSUInteger;
            let params = FftRadix4Params {
                log_s: log_s as u32,
                width: width as u32,
                quarter_height: quarter_h as u32,
            };
            enc.set_buffer(1, Some(&twiddle_bufs[tw_s_idx]), 0);
            enc.set_buffer(2, Some(&twiddle_bufs[tw_2s_idx]), 0);
            enc.set_bytes(
                3,
                std::mem::size_of::<FftRadix4Params>() as NSUInteger,
                (&params as *const FftRadix4Params) as *const _,
            );
            let tg_x = w.min(max_tg).max(1);
            let tg_y = ((max_tg / tg_x).max(1)).min(quarter_h);
            enc.dispatch_threads(MTLSize::new(w, quarter_h, 1), MTLSize::new(tg_x, tg_y, 1));
            layer += 2;
        } else {
            // Radix-2: one layer.
            enc.set_compute_pipeline_state(&ctx.fft_evals_layer_pipeline);
            let tw_idx = log_h - 1 - layer;
            let half_h = (height / 2) as NSUInteger;
            let params = FftLayerParams {
                log_stride: layer as u32,
                width: width as u32,
                half_height: half_h as u32,
            };
            enc.set_buffer(1, Some(&twiddle_bufs[tw_idx]), 0);
            enc.set_bytes(
                2,
                std::mem::size_of::<FftLayerParams>() as NSUInteger,
                (&params as *const FftLayerParams) as *const _,
            );
            let tg_x = w.min(max_tg).max(1);
            let tg_y = ((max_tg / tg_x).max(1)).min(half_h);
            enc.dispatch_threads(MTLSize::new(w, half_h, 1), MTLSize::new(tg_x, tg_y, 1));
            layer += 1;
        }
        pass += 1;
    }
    enc.end_encoding();

    cmd.commit();
    cmd.wait_until_completed();

    if !matrix_no_copy {
        unsafe {
            std::ptr::copy_nonoverlapping(matrix_buf.contents() as *const u32, matrix.as_mut_ptr(), matrix.len());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::{PrimeCharacteristicRing, TwoAdicField};
    use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
    use symetric::{Compression, precompute_zero_suffix_state};

    /// CPU reference of the same evals-DFT the GPU runs: in-place radix-2
    /// butterflies where layer `k` uses stride `2^k`. The butterfly is
    ///   t = (b - a) * twiddle
    ///   (a, b) -> (a + t, a - t)
    /// with a twiddle-free shortcut at offset 0 in each block.
    fn cpu_evals_fft_reference(matrix: &mut [KoalaBear], height: usize, width: usize) {
        assert_eq!(matrix.len(), height * width);
        let log_h = height.trailing_zeros() as usize;
        let generator = KoalaBear::two_adic_generator(log_h);
        // Build the same twiddle tables as EvalsDft::roots_of_unity_table.
        let half_n = height / 2;
        let mut nth_roots = Vec::with_capacity(half_n);
        let mut acc = KoalaBear::ONE;
        for _ in 0..half_n {
            nth_roots.push(acc);
            acc *= generator;
        }
        let twiddle_tables: Vec<Vec<KoalaBear>> = (0..log_h)
            .map(|i| nth_roots.iter().step_by(1 << i).copied().collect())
            .collect();

        for layer in 0..log_h {
            let stride = 1usize << layer;
            let twiddles = &twiddle_tables[log_h - 1 - layer];
            assert_eq!(twiddles.len(), stride);
            let block = 2 * stride;
            let n_blocks = height / block;
            for blk in 0..n_blocks {
                let base = blk * block;
                for i_off in 0..stride {
                    let row_a = base + i_off;
                    let row_b = row_a + stride;
                    let tw = twiddles[i_off];
                    for col in 0..width {
                        let a = matrix[row_a * width + col];
                        let b = matrix[row_b * width + col];
                        let t = if i_off == 0 { b - a } else { (b - a) * tw };
                        matrix[row_a * width + col] = a + t;
                        matrix[row_b * width + col] = a - t;
                    }
                }
            }
        }
    }

    fn make_twiddles_u32(height: usize) -> Vec<Vec<u32>> {
        let log_h = height.trailing_zeros() as usize;
        let generator = KoalaBear::two_adic_generator(log_h);
        let half_n = height / 2;
        let mut nth_roots = Vec::with_capacity(half_n);
        let mut acc = KoalaBear::ONE;
        for _ in 0..half_n {
            nth_roots.push(acc);
            acc *= generator;
        }
        (0..log_h)
            .map(|i| nth_roots.iter().step_by(1 << i).map(|x| kb_to_monty_u32(*x)).collect())
            .collect()
    }

    fn kb_arr_to_monty<const N: usize>(arr: [KoalaBear; N]) -> [u32; N] {
        arr.map(kb_to_monty_u32)
    }

    fn monty_to_kb_arr<const N: usize>(arr: [u32; N]) -> [KoalaBear; N] {
        // SAFETY: KoalaBear is #[repr(transparent)] over u32 (Montgomery form).
        unsafe { std::mem::transmute_copy(&arr) }
    }

    #[test]
    fn compress_parity_vs_cpu() {
        let p1 = default_koalabear_poseidon1_16();
        let cases: [[u32; 16]; 3] = [
            [0; 16],
            [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
            [
                0x12345678, 0xdeadbeef, 1, 0, 0x7effffff, 42, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000,
            ],
        ];

        let mut cpu_results = Vec::new();
        let mut gpu_inputs = Vec::new();
        for case in &cases {
            let kb_in = case.map(KoalaBear::new);
            gpu_inputs.push(kb_arr_to_monty(kb_in));
            let mut state = kb_in;
            p1.compress_mut(&mut state);
            cpu_results.push(kb_arr_to_monty(state));
        }

        let gpu_results = compress_many(&gpu_inputs);
        for (i, (cpu, gpu)) in cpu_results.iter().zip(gpu_results.iter()).enumerate() {
            assert_eq!(cpu, gpu, "mismatch on case {i}");
        }
    }

    #[test]
    fn hash_leaves_parity_vs_cpu() {
        let p1 = default_koalabear_poseidon1_16();

        let height = 16;
        let matrix_width = 21; // arbitrary, larger than effective
        let effective_base_width = 17;
        // Build a matrix of KoalaBear values (deterministic random-ish).
        let mut matrix_kb: Vec<KoalaBear> = (0..height * matrix_width)
            .map(|i| KoalaBear::new((i as u32).wrapping_mul(0x9e3779b1)))
            .collect();
        // Zero out the trailing columns so the CPU/GPU comparison is unambiguous.
        for r in 0..height {
            for c in effective_base_width..matrix_width {
                matrix_kb[r * matrix_width + c] = KoalaBear::ZERO;
            }
        }
        let matrix_u32: Vec<u32> = matrix_kb.iter().copied().map(kb_to_monty_u32).collect();

        // Build an "initial state" by absorbing one zero chunk into a fresh sponge.
        let n_zero_suffix_chunks = 2;
        let initial_state_kb = precompute_zero_suffix_state::<KoalaBear, _, 16, 8, 8>(&p1, n_zero_suffix_chunks);
        let initial_u32 = kb_arr_to_monty(initial_state_kb);

        // CPU reference: replicate the absorption logic.
        let n_pad = (8 - effective_base_width % 8) % 8;
        let mut cpu_digests = Vec::with_capacity(height);
        for r in 0..height {
            let mut state = initial_state_kb;
            // RTL stream: n_pad zeros, then v_{W-1}..v_0.
            let stream: Vec<KoalaBear> = (0..n_pad)
                .map(|_| KoalaBear::ZERO)
                .chain((0..effective_base_width).rev().map(|c| matrix_kb[r * matrix_width + c]))
                .collect();
            for chunk in stream.chunks(8) {
                for (j, v) in chunk.iter().copied().enumerate() {
                    state[15 - j] = v;
                }
                p1.compress_mut(&mut state);
            }
            let digest: [KoalaBear; 8] = state[..8].try_into().unwrap();
            cpu_digests.push(kb_arr_to_monty(digest));
        }

        let gpu_digests =
            hash_leaves_with_initial_state(&matrix_u32, height, matrix_width, effective_base_width, &initial_u32);
        for (i, (cpu, gpu)) in cpu_digests.iter().zip(gpu_digests.iter()).enumerate() {
            let cpu_kb = monty_to_kb_arr(*cpu);
            let gpu_kb = monty_to_kb_arr(*gpu);
            assert_eq!(cpu_kb, gpu_kb, "row {i} mismatch");
        }
    }

    #[test]
    fn no_initial_full_tree_parity_vs_cpu() {
        // Mirrors the WHIR open-rounds case: effective == full, no precomputed
        // initial state, first absorption fills the FULL Poseidon state.
        let p1 = default_koalabear_poseidon1_16();

        let height = 16;
        let matrix_width = 24; // < full so we exercise the leading-zero RTL pad
        let full_width = 32;
        let matrix_kb: Vec<KoalaBear> = (0..height * matrix_width)
            .map(|i| KoalaBear::new((i as u32).wrapping_mul(0x9e3779b1)))
            .collect();
        let matrix_u32: Vec<u32> = matrix_kb.iter().copied().map(kb_to_monty_u32).collect();

        // CPU reference using the exact same code path WHIR takes.
        let n_pad = full_width - matrix_width;
        let mut cpu_digests = Vec::with_capacity(height);
        for r in 0..height {
            // RTL stream of length `full_width`: leading zeros then matrix RTL.
            let stream: Vec<KoalaBear> = (0..n_pad)
                .map(|_| KoalaBear::ZERO)
                .chain((0..matrix_width).rev().map(|c| matrix_kb[r * matrix_width + c]))
                .collect();
            let digest: [KoalaBear; 8] =
                symetric::hash_rtl_iter::<KoalaBear, _, _, 16, 8, 8>(&p1, stream.into_iter().collect::<Vec<_>>());
            cpu_digests.push(kb_arr_to_monty(digest));
        }

        // GPU full tree.
        let gpu_layers = build_merkle_tree_full_no_initial(&matrix_u32, height, matrix_width, full_width);
        for (i, (cpu, gpu)) in cpu_digests.iter().zip(gpu_layers[0].iter()).enumerate() {
            let cpu_kb = monty_to_kb_arr(*cpu);
            let gpu_kb = monty_to_kb_arr(*gpu);
            assert_eq!(cpu_kb, gpu_kb, "leaf row {i} mismatch");
        }
    }

    #[test]
    fn fft_evals_in_place_parity_vs_cpu() {
        for &(log_h, width) in &[(1usize, 1usize), (2, 1), (3, 1), (5, 3), (8, 4), (10, 7)] {
            let height = 1usize << log_h;
            let mut cpu_mat: Vec<KoalaBear> = (0..height * width)
                .map(|i| KoalaBear::new((i as u32).wrapping_mul(0x9e3779b1) ^ 0xDEADu32))
                .collect();
            let mut gpu_mat_u32: Vec<u32> = cpu_mat.iter().copied().map(kb_to_monty_u32).collect();

            cpu_evals_fft_reference(&mut cpu_mat, height, width);

            let twiddles_owned = make_twiddles_u32(height);
            let twiddles: Vec<&[u32]> = twiddles_owned.iter().map(|v| v.as_slice()).collect();
            fft_evals_in_place_gpu(&mut gpu_mat_u32, height, width, &twiddles);

            for (i, (c, g)) in cpu_mat.iter().zip(gpu_mat_u32.iter()).enumerate() {
                let c_monty = kb_to_monty_u32(*c);
                if c_monty != *g {
                    eprintln!(
                        "log_h={log_h} w={width}: idx {i}: cpu={c_monty:#x} gpu={g:#x} (input was {:#x})",
                        kb_to_monty_u32(KoalaBear::new((i as u32).wrapping_mul(0x9e3779b1) ^ 0xDEADu32))
                    );
                }
                assert_eq!(c_monty, *g, "mismatch at idx {i} (log_h={log_h}, w={width})");
            }
        }
    }

    #[test]
    fn prepare_evals_parity_vs_cpu() {
        // Mirrors `prepare_evals_for_fft_unpacked`. We test the F (elem_size = 1) path.
        let log_block_size = 4;
        let block_size = 1usize << log_block_size;
        let log_inv_rate = 1;
        let n_blocks: usize = 4;
        let dft_n_cols = n_blocks; // dft_n_cols typically ≤ n_blocks
        let evals_len = (block_size * n_blocks) >> log_inv_rate;
        let evals: Vec<u32> = (0..evals_len as u32).map(|i| i.wrapping_mul(0x9e3779b1)).collect();
        let out_len = block_size * dft_n_cols;

        // CPU reference
        let cpu_out: Vec<u32> = (0..out_len)
            .map(|i| {
                let block_index = i % dft_n_cols;
                let offset_in_block = i / dft_n_cols;
                let src = ((block_index << log_block_size) + offset_in_block) >> log_inv_rate;
                evals[src]
            })
            .collect();

        let mut gpu_out = vec![0u32; out_len];
        prepare_evals_for_fft_gpu(&evals, &mut gpu_out, dft_n_cols, log_block_size, log_inv_rate, 1);
        assert_eq!(cpu_out, gpu_out);

        // Test EF case (elem_size = 5) by tripling the data and prepending a tag.
        let elem_size = 5usize;
        let evals_ef: Vec<u32> = (0..evals_len * elem_size)
            .map(|i| (i as u32).wrapping_mul(0x85ebca6bu32))
            .collect();
        let cpu_out_ef: Vec<u32> = (0..out_len)
            .flat_map(|i| {
                let block_index = i % dft_n_cols;
                let offset_in_block = i / dft_n_cols;
                let src = ((block_index << log_block_size) + offset_in_block) >> log_inv_rate;
                evals_ef[src * elem_size..(src + 1) * elem_size].to_vec()
            })
            .collect();
        let mut gpu_out_ef = vec![0u32; out_len * elem_size];
        prepare_evals_for_fft_gpu(
            &evals_ef,
            &mut gpu_out_ef,
            dft_n_cols,
            log_block_size,
            log_inv_rate,
            elem_size,
        );
        assert_eq!(cpu_out_ef, gpu_out_ef);
    }
}
