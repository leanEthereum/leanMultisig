from snark_lib import *


def main():
    assert test_func(1, 0) == 11
    assert test_func(1, 1) == 20
    assert test_func(0, 0) == 100
    return


def test_func(cond, selector):
    x: Mut = 10
    if cond == 1:
        match selector:
            case 0:
                x = x + 1
            case 1:
                x = x + 10
    else:
        x = x + 90
    return x
