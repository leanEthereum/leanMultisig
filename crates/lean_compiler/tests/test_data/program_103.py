from snark_lib import *


def main():
    arr = Array(5)
    for i in unroll(0, 5):
        arr[i] = i * 10

    idx: Mut = 0
    val1 = arr[idx]  # arr[0] = 0
    assert val1 == 0

    idx = idx + 1
    val2 = arr[idx]  # arr[1] = 10
    assert val2 == 10

    idx = idx + 2
    val3 = arr[idx]  # arr[3] = 30
    assert val3 == 30

    return
