from snark_lib import *


def main():
    a: Mut = 1
    b: Mut = 2
    a, b = swap(a, b)
    assert a == 2
    assert b == 1

    a, b = swap(a, b)
    assert a == 1
    assert b == 2

    c: Mut = compute(a, b)
    assert c == 5  # 1 + 2*2 = 5
    c = compute(c, c)
    assert c == 15  # 5 + 5*2 = 15
    return


def swap(x, y):
    return y, x


def compute(x, y):
    result = x + y * 2
    return result
