from snark_lib import *
from ..zkdsl_implem.utils import *
from ..zkdsl_implem.jagged_bp import *

# Sized BP-eval inputs come in via witness hints (because the public
# input is fixed-size DIGEST_LEN base scalars and we need variable-length
# EF arrays). The public input only carries the four scalar sizes.
#
# Public input layout:
#   [0] log_width
#   [1] log_dense_size
#   [2] z_row_len
#   [3] z_col_len
#   [4..8] zero pad
#
# Hints (named):
#   "z_row"    : z_row_len    * DIM base scalars
#   "z_col"    : z_col_len    * DIM base scalars
#   "z_index"  : log_dense_size * DIM base scalars
#   "t_prev"   : log_dense_size * DIM base scalars
#   "t_next"   : log_dense_size * DIM base scalars
#   "expected" : DIM base scalars


def main():
    build_preamble_memory()
    pub_mem = 0
    log_width = pub_mem[0]
    log_dense_size = pub_mem[1]
    z_row_len = pub_mem[2]
    z_col_len = pub_mem[3]

    z_row = Array(z_row_len * DIM)
    hint_witness("z_row", z_row)
    z_col = Array(z_col_len * DIM)
    hint_witness("z_col", z_col)
    z_index = Array(log_dense_size * DIM)
    hint_witness("z_index", z_index)
    t_prev = Array(log_dense_size * DIM)
    hint_witness("t_prev", t_prev)
    t_next = Array(log_dense_size * DIM)
    hint_witness("t_next", t_next)
    expected = Array(DIM)
    hint_witness("expected", expected)

    result = bp_eval(z_row, z_row_len, z_col, z_col_len, z_index, t_prev, t_next, log_width, log_dense_size)

    for k in unroll(0, DIM):
        assert result[k] == expected[k]
    return
