from snark_lib import *


def main():
    total: Mut = 0
    outer_sum: Mut = 0
    for i in unroll(0, 3):
        outer_sum = outer_sum + i
        inner_sum: Mut = 0
        for j in unroll(0, 4):
            inner_sum = inner_sum + j
            total = total + 1
        assert inner_sum == 6
    assert outer_sum == 3
    assert total == 12
    return
