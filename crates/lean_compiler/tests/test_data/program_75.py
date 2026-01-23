from snark_lib import *


def main():
    assert test_func(0, 1) == 11
    assert test_func(0, 0) == 20
    assert test_func(1, 1) == 110
    assert test_func(1, 0) == 200
    return


def test_func(selector, cond):
    x: Mut = 10
    match selector:
        case 0:
            if cond == 1:
                x = x + 1
            else:
                x = x + 10
        case 1:
            if cond == 1:
                x = x + 100
            else:
                x = x + 190
    return x
