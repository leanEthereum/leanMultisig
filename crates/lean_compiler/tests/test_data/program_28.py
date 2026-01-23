from snark_lib import *


def main():
    a = Array(10)
    b = Array(10)
    a[1], b[4] = get_two_values()
    assert a[1] == 42
    assert b[4] == 99

    i = 2
    j = 3
    a[i], b[j] = get_two_values()
    assert a[2] == 42
    assert b[3] == 99

    x, a[5] = get_two_values()
    assert x == 42
    assert a[5] == 99

    return


def get_two_values():
    return 42, 99
