from snark_lib import *


def main():
    a: Mut = 10
    b: Mut = 20

    temp = a
    a = b
    b = temp

    assert a == 20
    assert b == 10

    temp2 = a
    a = b
    b = temp2

    assert a == 10
    assert b == 20
    return
