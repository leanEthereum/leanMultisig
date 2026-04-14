from snark_lib import *


def main():
    p = 0
    mode = p[0]
    x = p[1]
    y = p[2]
    expected = p[3]
    secondary = p[4]
    flag = p[5]
    offset = p[6]
    total = p[7]

    computed: Imu
    match mode:
        case 0:
            computed = add_op(x, y)
        case 1:
            computed = sub_op(x, y)
        case 2:
            computed = mul_op(x, y)
        case 3:
            computed = combined(x, y)
    assert computed == expected

    adjusted: Imu
    if flag == 0:
        adjusted = bump(secondary, 1)
    elif flag == 1:
        adjusted = bump(secondary, 10)
    else:
        adjusted = bump(secondary, 100)
    assert adjusted == offset

    assert total == expected + offset
    return


def add_op(a, b):
    return a + b


def sub_op(a, b):
    return a - b


def mul_op(a, b):
    return a * b


def combined(a, b):
    return mul_op(a, b) + add_op(a, b)


@inline
def bump(v, k):
    return v + k
