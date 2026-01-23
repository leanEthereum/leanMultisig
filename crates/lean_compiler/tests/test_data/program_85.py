from snark_lib import *


def main():
    assert test_func(0, 0) == 111
    assert test_func(0, 1) == 121
    assert test_func(1, 0) == 211
    assert test_func(1, 1) == 221
    return


def test_func(a, b):
    x: Mut = 100
    match a:
        case 0:
            x = x + 10
            match b:
                case 0:
                    x = x + 1
                case 1:
                    x = x + 11
        case 1:
            x = x + 110
            match b:
                case 0:
                    x = x + 1
                case 1:
                    x = x + 11
    return x
