from snark_lib import *


def main():
    outer_sum: Mut = 0
    for i in unroll(0, 3):
        inner_sum: Mut = 0
        for j in unroll(0, 4):
            inner_sum = inner_sum + j
        outer_sum = outer_sum + inner_sum
    assert outer_sum == 18
    return
