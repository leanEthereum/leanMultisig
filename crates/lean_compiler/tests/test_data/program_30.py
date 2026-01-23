from snark_lib import *

ARR = [10, 100]


def main():
    buff = Array(3)
    buff[0] = 0
    for i in unroll(0, 2):
        res = f1(ARR[i])
        buff[i + 1] = res
    assert buff[2] == 1390320454
    return


def f1(x: Const):
    buff = Array(9)
    buff[0] = 1
    for i in unroll(x, x + 4):
        for j in unroll(i, i + 2):
            index = (i - x) * 2 + (j - i)
            res = f2(i, j)
            buff[index + 1] = buff[index] * res
    return buff[8]


def f2(x: Const, y: Const):
    buff = Array(7)
    buff[0] = 0
    for i in unroll(x, x + 2):
        for j in unroll(i, i + 3):
            index = (i - x) * 3 + (j - i)
            buff[index + 1] = buff[index] + i + j
    return buff[4]
