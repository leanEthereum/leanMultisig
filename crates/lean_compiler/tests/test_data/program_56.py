from snark_lib import *

WEIGHTS = [1, 2, 3, 4, 5]
N = 5


def main():
    weighted_sum: Mut = 0
    for i in unroll(0, N):
        weighted_sum = weighted_sum + WEIGHTS[i] * (i + 1)
    assert weighted_sum == 55
    return
