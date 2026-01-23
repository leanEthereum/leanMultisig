from snark_lib import *


def main():
    a: Mut = 10
    b: Mut = 20

    cond = 1
    if cond == 1:
        a = b + 1  # a = 21
        b = a + 1  # b = 22 (uses new a)
    else:
        b = a + 100
        a = b + 1

    assert a == 21
    assert b == 22
    return
