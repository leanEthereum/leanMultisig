from snark_lib import *

FIVE = 5
ARR = [4, FIVE, 4 + 2, 3 * 2 + 1]


def main():
    for i in unroll(1, len(ARR)):
        x = i + 4
        assert ARR[i] == x
    four = 4
    assert len(ARR) == four
    res = func(2)
    six = 6
    assert res == six
    nothing(ARR[0])
    mem_arr = Array(len(ARR))
    for i in unroll(0, len(ARR)):
        mem_arr[i] = ARR[i]
    for i in range(0, ARR[0]):
        print(2 ** ARR[0])
    print(2 ** ARR[1])
    return


def func(x: Const):
    return ARR[x]


def nothing(x):
    return
