from snark_lib import *


def main():
    a = double(next_multiple_of(12, 8))
    assert a == 32
    return


def double(n: Const):
    return next_multiple_of(n, n) * 2
