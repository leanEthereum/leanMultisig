from snark_lib import *


def main():
    assert test_func(0) == 11
    assert test_func(1) == 12
    assert test_func(2) == 13
    return


def test_func(sel):
    x: Mut = 10
    match sel:
        case 0:
            x = x + 1
        case 1:
            x = x + 1
            x = x + 1
        case 2:
            x = x + 1
            x = x + 1
            x = x + 1
    return x
