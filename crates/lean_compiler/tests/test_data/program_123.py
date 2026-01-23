from snark_lib import *


def main():
    r1 = many_assigns()
    assert r1 == 256

    r2 = self_referential()
    assert r2 == 120

    a, b, c, d = quad_assign()
    assert a == 10
    assert b == 20
    assert c == 30
    assert d == 40

    r3 = interleaved_ops()
    assert r3 == 100

    r4 = dependency_chain()
    assert r4 == 55

    return


def many_assigns():
    x: Mut = 1
    x = 2
    x = 4
    x = 8
    x = 16
    x = 32
    x = 64
    x = 128
    x = 256
    return x


def self_referential():
    x: Mut = 1
    x = x * 2  # 2
    x = x * 3  # 6
    x = x * 4  # 24
    x = x * 5  # 120
    return x


def quad_assign():
    a: Mut = 0
    b: Mut = 0
    c: Mut = 0
    d: Mut = 0

    a = 10
    b = 20
    c = 30
    d = 40

    return a, b, c, d


def interleaved_ops():
    x: Mut = 5
    y: Mut = 10

    temp = x + y  # Read both: 15
    x = temp  # x = 15
    temp2 = x * 2  # Read x: 30
    y = temp2  # y = 30
    x = y + x  # x = 30 + 15 = 45
    y = x + y  # y = 45 + 30 = 75
    x = y + 25  # x = 100

    return x


def dependency_chain():
    x: Mut = 1
    x = x + 2  # 3
    x = x + 4  # 7
    x = x + 8  # 15
    x = x + 16  # 31
    x = x + 24  # 55
    return x
