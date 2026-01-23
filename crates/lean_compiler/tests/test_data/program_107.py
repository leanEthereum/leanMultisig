from snark_lib import *


def main():
    assert test_func(0, 1) == 111
    assert test_func(1, 0) == 200
    return


def test_func(sel, cond):
    x: Mut = 100

    match sel:
        case 0:
            x = x + 10
        case 1:
            x = x + 100

    if cond == 1:
        x = x + 1

    return x
