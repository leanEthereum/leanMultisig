from snark_lib import *
# Test: Mix of unrolled outer loop and non-unrolled inner loop with mutable vars


def main():
    total: Mut = 0
    for i in unroll(0, 3):
        # Inner loop is non-unrolled, uses mutable variable
        inner_sum: Mut = 0
        for j in range(0, 4):
            inner_sum += j + i
        total += inner_sum
    # i=0: inner_sum = 0+1+2+3 = 6, total = 6
    # i=1: inner_sum = 1+2+3+4 = 10, total = 16
    # i=2: inner_sum = 2+3+4+5 = 14, total = 30
    assert total == 30
    return
