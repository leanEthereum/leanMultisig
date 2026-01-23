from snark_lib import *


def add_four(a, b, c, d):
    return a + b + c + d


def multi_return(a, b):
    return (
        a + 1,
        b + 2,
        a + b,
    )


def multi_line_params(
    a,
    b: Mut,
    c: Const,
):
    return a + b + c


def main():
    result = add_four(1, 2, 3, 4)
    assert result == 10

    arr = DynArray([1, 2, 3])
    assert arr[0] == 1
    assert arr[1] == 2
    assert arr[2] == 3

    nested = add_four(1, add_four(10, 20, 30, 40), 2, 3)
    assert nested == 106

    x = 5
    y = 10
    z: Imu
    if x + y == 15:
        z = 1
    else:
        z = 0
    assert z == 1

    w: Imu
    if x + y * 2 == 25:
        w = 100
    else:
        w = 0
    assert w == 100

    r1, r2, r3 = multi_return(10, 20)
    assert r1 == 11
    assert r2 == 22
    assert r3 == 30

    assert r1 == 11
    assert r2 + r3 == 52

    (s1, s2, s3) = multi_return(100, 200)
    assert s1 == 101
    assert s2 == 202
    assert s3 == 300

    mlp = multi_line_params(1, 2, 3)
    assert mlp == 6
    return
