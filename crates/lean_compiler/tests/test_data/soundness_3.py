from snark_lib import *


def main():
    p = 0
    n = p[0]
    seed = p[1]
    sum_expected = p[2]
    prod_expected = p[3]
    max_val = p[4]
    upper = p[5]
    w = p[6]
    expected_final = p[7]

    assert n == 4

    arr = Array(4)
    for i in unroll(0, 4):
        arr[i] = seed + i

    s: Mut = 0
    for i in range(0, 4):
        s = s + arr[i]
    assert s == sum_expected

    prod: Mut = 1
    for i in unroll(0, 4):
        prod = times(prod, arr[i])
    assert prod == prod_expected

    assert max_val < upper
    assert upper <= 100
    assert upper == max_val + 5
    assert w + max_val == expected_final
    return


@inline
def times(a, b):
    return a * b
