from snark_lib import *


def main():
    assert test_func(0, 0) == 6
    return


def test_func(a, b):
    x = 1

    mut_x_2: Imu
    match a:
        case 0:
            mut_x_1: Imu
            mut_x_1 = x + 2
            match b:
                case 0:
                    mut_x_2 = mut_x_1 + 3

    return mut_x_2
