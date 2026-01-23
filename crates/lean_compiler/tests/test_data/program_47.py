from snark_lib import *


def main():
    count: Mut = 0
    sum_i: Mut = 0
    sum_j: Mut = 0
    sum_k: Mut = 0
    for i in unroll(0, 2):
        sum_i = sum_i + i
        for j in unroll(0, 3):
            sum_j = sum_j + j
            for k in unroll(0, 2):
                sum_k = sum_k + k
                count = count + 1
    assert count == 12
    assert sum_i == 1
    assert sum_j == 6
    assert sum_k == 6
    return
