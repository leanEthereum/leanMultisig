from snark_lib import *

NESTED = [[1, 2], [3, 4, 5], [6]]


def main():
    assert len(NESTED) == 3
    assert len(NESTED[0]) == 2
    assert len(NESTED[1]) == 3
    assert len(NESTED[2]) == 1

    assert NESTED[0][0] == 1
    assert NESTED[0][1] == 2
    assert NESTED[1][0] == 3
    assert NESTED[1][2] == 5
    assert NESTED[2][0] == 6

    return
