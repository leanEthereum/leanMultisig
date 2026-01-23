from snark_lib import *


def main():
    arr = Array(20)
    for i in range(0, 5):
        arr[i * 2], arr[i * 2 + 1] = compute_pair(i)
    assert arr[0] == 0
    assert arr[1] == 0
    assert arr[2] == 1
    assert arr[3] == 2
    assert arr[4] == 2
    assert arr[5] == 4
    return


def compute_pair(n):
    return n, n * 2
