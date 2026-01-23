from snark_lib import *


def main():
    arr = Array(10)
    arr[6] = 42
    arr[8] = 11
    sum_1 = func_1(arr[6], arr[8])
    assert sum_1 == 53
    return


@inline
def func_1(i, j):
    for k in range(0, i):
        for u in range(0, j):
            assert k + u != 1000000
    return i + j
