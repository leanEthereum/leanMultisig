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

inline uint dot16(thread const uint *state, constant uint *row) {
    uint acc = kb_mul(state[0], row[0]);
    for (int i = 1; i < 16; i++) {
        acc = kb_add(acc, kb_mul(state[i], row[i]));
    }
    return acc;
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
    for (int r = 0; r < 4; r++) {
        full_round(state, &INITIAL_RC[r * 16]);
    }
    for (int i = 0; i < 16; i++) {
        state[i] = kb_add(state[i], SPARSE_FIRST_RC[i]);
    }
    uint tmp[16];
    for (int i = 0; i < 16; i++) {
        tmp[i] = dot16(state, &SPARSE_M_I[i * 16]);
    }
    for (int i = 0; i < 16; i++) state[i] = tmp[i];

    for (int r = 0; r < 20; r++) {
        state[0] = cube(state[0]);
        if (r < 19) {
            state[0] = kb_add(state[0], SPARSE_SCALAR_RC[r]);
        }
        uint old_s0 = state[0];
        state[0] = dot16(state, &SPARSE_FIRST_ROW[r * 16]);
        for (int i = 1; i < 16; i++) {
            state[i] = kb_add(state[i], kb_mul(old_s0, SPARSE_V[r * 16 + (i - 1)]));
        }
    }

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
    Ok(MetalCtx {
        device,
        queue,
        compress_one_pipeline,
        compress_chain_pipeline,
        compress_pairs_pipeline,
        hash_leaves_pipeline,
        hash_leaves_no_initial_pipeline,
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

    let tg_size = ctx.compress_chain_pipeline.max_total_threads_per_threadgroup().min(64);

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

    let tg_size = ctx.compress_one_pipeline.max_total_threads_per_threadgroup().min(64);
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

    let tg_size = ctx.hash_leaves_pipeline.max_total_threads_per_threadgroup().min(64);
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
        let tg = ctx.hash_leaves_pipeline.max_total_threads_per_threadgroup().min(64);
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
            .min(64)
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
            .min(64)
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

#[cfg(test)]
mod tests {
    use super::*;
    use field::PrimeCharacteristicRing;
    use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
    use symetric::{Compression, precompute_zero_suffix_state};

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
}
