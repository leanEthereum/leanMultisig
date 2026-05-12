from snark_lib import *
from ..zkdsl_implem.utils import *
from ..zkdsl_implem.jagged_bp import *

# Multi-claim summation validation. Mirrors the per-claim accumulation
# loop in `jagged_verify::eval_f_at_final`:
#   F(i*) = sum_j alpha_j * BP_eval(z_row_j, z_col_j, i*, t_prev_j, t_next_j)
#
# To keep the zkDSL plumbing tractable, this test fixes the per-claim
# structure (`log_width`, `is_next`, etc.) at compile time -- which
# matches how the real recursion verifier knows the claim structure (the
# loop over claims is itself `unroll`-style, with each claim's metadata
# baked into the bytecode via const arrays).
#
# We test two claims:
#   * claim 0: sub_table 0, log_width=2 (4 cols), col=1, is_next=False
#   * claim 1: sub_table 0, log_width=2 (4 cols), col=3, is_next=True
#
# Inputs:
#   public input: M (= log_dense_size), z_row_len, pad
#   hints (all base-field arrays, lifted to EF inside):
#     "z_row_0"        : z_row_len * DIM   - claim 0's z_row
#     "z_row_1"        : z_row_len * DIM   - claim 1's z_row
#     "z_index"        : M * DIM           - i*
#     "t_prev_bits"    : M                 - sub-table 0's cumulative-area (bits)
#     "t_prev_shifted_bits": M             - t_prev_bits + 2^log_width
#     "t_next_bits"    : M                 - sub-table 1's cumulative-area (= next-of-sub-table-0)
#     "alpha_0"        : DIM
#     "alpha_1"        : DIM
#     "expected"       : DIM
#
# Sizes used in this test (chosen small to make compile + execute fast):
#   M (log_dense_size) = 8
#   log_width          = 2
#   z_row_len          = 6  (= M - log_width)


M_LOG_DENSE = 8
LOG_WIDTH = 2
Z_ROW_LEN = 6  # = M - LOG_WIDTH
COL_0 = 1
COL_1 = 3


def lift_bits_to_ef(bits_ptr, n_bits, out_ptr):
    """Lift `n_bits` boolean base-field bits to EF representation (each
    bit becomes `[bit, 0, 0, 0, 0]`). Caller passes preallocated
    `out_ptr` of size `n_bits * DIM`."""
    for k in unroll(0, M_LOG_DENSE):
        out_ptr[k * DIM] = bits_ptr[k]
        for kk in unroll(1, DIM):
            out_ptr[k * DIM + kk] = 0
    return


def col_to_z_col_ptr(col: Const, log_width: Const):
    """Build the big-endian boolean point of `col` in `log_width` bits,
    as a `log_width * DIM` EF array. `col` and `log_width` are
    compile-time constants so we can fully unroll. The zkDSL doesn't
    have shift/mask operators, so we extract bit `i` via
    `(col / 2**i) % 2`."""
    z_col = Array(log_width * DIM)
    for k in unroll(0, log_width):
        # Big-endian: position k holds bit (log_width - 1 - k) of col.
        bit_value = (col / 2 ** (log_width - 1 - k)) % 2
        z_col[k * DIM] = bit_value
        for kk in unroll(1, DIM):
            z_col[k * DIM + kk] = 0
    return z_col


def main():
    build_preamble_memory()

    z_row_0 = Array(Z_ROW_LEN * DIM)
    hint_witness("z_row_0", z_row_0)
    z_row_1 = Array(Z_ROW_LEN * DIM)
    hint_witness("z_row_1", z_row_1)
    z_index = Array(M_LOG_DENSE * DIM)
    hint_witness("z_index", z_index)

    t_prev_bits = Array(M_LOG_DENSE)
    hint_witness("t_prev_bits", t_prev_bits)
    t_prev_shifted_bits = Array(M_LOG_DENSE)
    hint_witness("t_prev_shifted_bits", t_prev_shifted_bits)
    t_next_bits = Array(M_LOG_DENSE)
    hint_witness("t_next_bits", t_next_bits)

    alpha_0 = Array(DIM)
    hint_witness("alpha_0", alpha_0)
    alpha_1 = Array(DIM)
    hint_witness("alpha_1", alpha_1)
    expected = Array(DIM)
    hint_witness("expected", expected)

    # Lift bit arrays to EF.
    t_prev_ef = Array(M_LOG_DENSE * DIM)
    lift_bits_to_ef(t_prev_bits, M_LOG_DENSE, t_prev_ef)
    t_prev_shifted_ef = Array(M_LOG_DENSE * DIM)
    lift_bits_to_ef(t_prev_shifted_bits, M_LOG_DENSE, t_prev_shifted_ef)
    t_next_ef = Array(M_LOG_DENSE * DIM)
    lift_bits_to_ef(t_next_bits, M_LOG_DENSE, t_next_ef)

    # Claim 0: regular (is_next=False), col=COL_0.
    z_col_0 = col_to_z_col_ptr(COL_0, LOG_WIDTH)
    bp_0 = bp_eval(z_row_0, Z_ROW_LEN, z_col_0, LOG_WIDTH, z_index, t_prev_ef, t_next_ef, LOG_WIDTH, M_LOG_DENSE)

    # Claim 1: next-claim (is_next=True), col=COL_1.
    z_col_1 = col_to_z_col_ptr(COL_1, LOG_WIDTH)
    bp_1 = bp_eval(z_row_1, Z_ROW_LEN, z_col_1, LOG_WIDTH, z_index, t_prev_shifted_ef, t_next_ef, LOG_WIDTH, M_LOG_DENSE)

    # F(i*) = alpha_0 * bp_0 + alpha_1 * bp_1
    term_0 = mul_extension_ret(alpha_0, bp_0)
    term_1 = mul_extension_ret(alpha_1, bp_1)
    f_at_istar = add_extension_ret(term_0, term_1)

    for k in unroll(0, DIM):
        assert f_at_istar[k] == expected[k]
    return
