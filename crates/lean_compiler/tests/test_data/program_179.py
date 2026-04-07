from snark_lib import *

# Exercise the memcopy4 precompile:
#     memcopy4(addr_in, addr_out, stride_in, n_reps)
# copies 4 field elements n_reps times, advancing source by stride_in
# (must be 0 or 4) and destination by 8 (hardcoded) per iteration.

N_REPS = 3
STRIDE_IN = 4
STRIDE_OUT = 8
SRC_LEN = (N_REPS - 1) * STRIDE_IN + 4  # 8 + 4 = 12
DST_LEN = (N_REPS - 1) * STRIDE_OUT + 4  # 16 + 4 = 20


def main():
    src = Array(SRC_LEN)
    for i in unroll(0, SRC_LEN):
        src[i] = i * 7 + 1

    dst = Array(DST_LEN)
    memcopy4(src, dst, STRIDE_IN, N_REPS)

    for i in unroll(0, N_REPS):
        for k in unroll(0, 4):
            assert dst[i * STRIDE_OUT + k] == src[i * STRIDE_IN + k]

    # Broadcast variant: stride_in=0, n_reps=2
    src2 = Array(4)
    for i in unroll(0, 4):
        src2[i] = i + 100
    dst2 = Array(12)  # (2-1)*8 + 4 = 12
    memcopy4(src2, dst2, 0, 2)
    for k in unroll(0, 4):
        assert dst2[k] == src2[k]
        assert dst2[8 + k] == src2[k]

    return
