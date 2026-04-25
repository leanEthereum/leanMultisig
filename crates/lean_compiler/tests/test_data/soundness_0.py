from snark_lib import *


def main():
    p = 0
    a = p[0]
    b = p[1]
    c = p[2]
    d = p[3]
    e = p[4]
    f = p[5]
    g = p[6]
    h = p[7]

    assert double(a) == b
    assert square_plus_one(a) == d
    assert a + c == 10
    assert e < 10
    assert f <= 20

    acc: Mut = 0
    for i in unroll(0, 4):
        acc = acc + p[i]
    assert acc == g

    if h == 1:
        assert a + b == 9
    else:
        assert a == 0
    return


@inline
def double(x):
    return x + x


def square_plus_one(x):
    return x * x + 1
