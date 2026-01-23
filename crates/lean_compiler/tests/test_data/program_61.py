from snark_lib import *


def main():
    a: Mut = 1
    b: Mut = 2
    c: Mut = 3

    a, b = double_both(a, b)
    assert a == 2
    assert b == 4

    b, c = double_both(b, c)
    assert b == 8
    assert c == 6

    a, c = double_both(a, c)
    assert a == 4
    assert c == 12

    assert a + b + c == 24
    return


def double_both(x, y):
    return x * 2, y * 2
