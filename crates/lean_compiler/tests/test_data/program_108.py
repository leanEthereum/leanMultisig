from snark_lib import *


def main():
    assert test_func(0, 0) == 6
    return


def test_func(a, b):
    x: Mut = 1
    match a:
        case 0:
            x = x + 2
            match b:
                case 0:
                    x = x + 3
    return x
