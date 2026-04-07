from snark_lib import *

# Exercise the memcopy_4 precompile:
#     memcopy_4(addr_in, addr_out, stride_in, n_reps)
# copies n_reps contiguous 5-element chunks from `addr_in` to `addr_out`,
# advancing the source by `stride_in` (must be 0 or 4) and the destination
# by 8 (hardcoded) per iteration.

N_REPS = 3
STRIDE_IN = 4
STRIDE_OUT = 8  # hardcoded in the precompile
SRC_LEN = (N_REPS - 1) * STRIDE_IN + 5  # 8 + 5 = 13
DST_LEN = (N_REPS - 1) * STRIDE_OUT + 5  # 16 + 5 = 21


def main():
    src = Array(SRC_LEN)
    for i in unroll(0, SRC_LEN):
        src[i] = i * 7 + 1

    dst = Array(DST_LEN)
    memcopy_4(src, dst, STRIDE_IN, N_REPS)

    # Each iteration writes 5 elements. Verify chunk-by-chunk.
    for i in unroll(0, N_REPS):
        for k in unroll(0, 5):
            assert dst[i * STRIDE_OUT + k] == src[i * STRIDE_IN + k]

    # Also exercise the stride_in=0 (broadcast) variant.
    src2 = Array(5)
    for i in unroll(0, 5):
        src2[i] = i + 100
    dst2 = Array(13)  # (2-1)*8 + 5 = 13
    memcopy_4(src2, dst2, 0, 2)
    # Both destination chunks should be equal to the single source chunk.
    for k in unroll(0, 5):
        assert dst2[k] == src2[k]
        assert dst2[8 + k] == src2[k]

    return
