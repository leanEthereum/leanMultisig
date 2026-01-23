from snark_lib import *


def main():
    assert incr(incr(incr(1))) == 4
    x = add(incr(1), incr(2))
    assert x == 5

    assert incr_inlined(incr_inlined(incr_inlined(1))) == 4
    y = add_inlined(incr_inlined(1), add_inlined(incr_inlined(2), incr_inlined(2)))
    assert y == 8

    return


def add(a, b):
    return a + b


def incr(x):
    return x + 1


@inline
def incr_inlined(x):
    return x + 1


@inline
def add_inlined(a, b):
    c = Array(1)
    zero = 0
    c[zero] = a + b
    return c[0]
