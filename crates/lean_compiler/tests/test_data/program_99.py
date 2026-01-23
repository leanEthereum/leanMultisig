from snark_lib import *


def main():
    result = accumulate(5)
    assert result == 8
    return


def accumulate(x: Mut):
    for i in unroll(0, 3):
        x = x + i
    return x
