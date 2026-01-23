from snark_lib import *


def main():
    a: Mut = 5
    b: Mut = 3

    a = a * a + b * b  # 25 + 9 = 34
    assert a == 34

    b = a - b * 2  # 34 - 6 = 28
    assert b == 28

    c: Mut = a + b  # 34 + 28 = 62
    assert c == 62

    c = c + 8  # 70
    assert c == 70

    c = c - 10  # 60
    assert c == 60
    return
