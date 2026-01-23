from snark_lib import *


def main():
    a: Mut = 0
    b: Mut = 0
    c: Mut = 0

    cond = 1
    if cond == 1:
        a = a + 1
        b = b + 10
    else:
        b = b + 20
        c = c + 100

    assert a == 1
    assert b == 10
    assert c == 0
    return
