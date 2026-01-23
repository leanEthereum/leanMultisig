from snark_lib import *


def main():
    a: Mut = 5
    b: Mut = 10

    a += 3
    assert a == 8

    a -= 2
    assert a == 6

    a *= 4
    assert a == 24

    a /= 3
    assert a == 8

    b += a
    assert b == 18

    b -= 3
    b *= 2
    assert b == 30

    c: Mut = 100
    c /= 4
    c -= 5
    c += 10
    c *= 3
    assert c == 90

    return
