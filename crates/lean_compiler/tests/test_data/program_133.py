from snark_lib import *
# Test: Nested non-unrolled loops with mutable variables
# Computes sum of i*j for i in 0..3, j in 0..4


def main():
    total: Mut = 0
    for i in range(0, 3):
        for j in range(0, 4):
            total += i * j
    # i=0: 0*0 + 0*1 + 0*2 + 0*3 = 0
    # i=1: 1*0 + 1*1 + 1*2 + 1*3 = 6
    # i=2: 2*0 + 2*1 + 2*2 + 2*3 = 12
    # total = 0 + 6 + 12 = 18
    assert total == 18
    return
