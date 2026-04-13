from snark_lib import *


def main():
    p = 0
    n = p[0]
    sum_range = p[1]
    x = p[2]
    y = p[3]
    prod_xy = p[4]
    outer = p[5]
    inner_bound = p[6]
    v = p[7]

    assert n == 5

    s: Mut = 0
    for i in range(0, 5):
        s = s + i
    assert s == sum_range

    assert mul(x, y) == prod_xy

    nested: Mut = 0
    for i in unroll(0, 3):
        for j in unroll(0, 3):
            nested = nested + i * j
    assert nested == outer

    assert v < inner_bound
    assert inner_bound == v + 1
    return


def mul(a, b):
    return a * b
