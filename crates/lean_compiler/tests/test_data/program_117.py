from snark_lib import *


def main():
    result1 = multi_ops()
    assert result1 == 42

    result2 = double_use_expr()
    assert result2 == 18

    a, b, c = cascade_assign()
    assert a == 3
    assert b == 6
    assert c == 18

    result4 = mixed_mut_immut()
    assert result4 == 35

    result5 = expr_tree()
    assert result5 == 100

    return


def multi_ops():
    x: Mut = 2
    x = x + 3  # 5
    x = x * 4  # 20
    x = x + 2  # 22
    x = x * 2  # 44
    x = x - 2  # 42
    return x


def double_use_expr():
    x: Mut = 3
    y = x + x * 2  # 3 + 6 = 9
    x = y  # x = 9
    z = x + x  # 18
    return z


def cascade_assign():
    a: Mut = 1
    b: Mut = 2
    c: Mut = 3

    a = a + 2  # a = 3
    b = a * 2  # b = 6
    c = b * 3  # c = 18

    return a, b, c


def mixed_mut_immut():
    immut_x = 10
    y: Mut = 5

    y = y + immut_x  # 15
    y = y + immut_x  # 25
    y = y + immut_x  # 35

    return y


def expr_tree():
    a: Mut = 2
    b: Mut = 3
    c: Mut = 5

    a = a * b + c  # 2*3 + 5 = 11
    b = a + c  # 11 + 5 = 16
    c = a * b - (a + b)  # 11*16 - 27 = 176 - 27 = 149

    a = 10
    b = a
    c = a * b  # 100

    return c
