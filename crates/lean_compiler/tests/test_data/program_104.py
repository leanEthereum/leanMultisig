from snark_lib import *


def main():
    a: Mut = 1
    b: Mut = 2

    a, b = pair_incr(a, b)  # a=2, b=3
    assert a == 2
    assert b == 3

    a, b = pair_incr(a, b)  # a=3, b=4
    assert a == 3
    assert b == 4

    a, b = pair_swap(a, b)  # a=4, b=3
    assert a == 4
    assert b == 3

    return


def pair_incr(x, y):
    return x + 1, y + 1


def pair_swap(x, y):
    return y, x
