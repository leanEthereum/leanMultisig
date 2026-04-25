from snark_lib import *

ONE_EF_PTR = 1  # right after the (empty-public-input) zero-padded cell at memory[0]


def main():
    init_one_ef()
    x = 1
    y = 2
    i, j, k = func_1(x, y)
    assert i == 2
    assert j == 3
    assert k == 4194304000

    g = Array(8)
    h = Array(8)
    for i in range(0, 8):
        g[i] = i
    for i in unroll(0, 8):
        h[i] = i
    assert_eq_1(g, h)
    assert_eq_2(g, h)
    assert_eq_3(g, h)
    assert_eq_4(g, h)
    assert_eq_5(g, h)
    return


@inline
def func_1(a, b):
    x = a * b
    y = a + b
    return x, y, a - b


def assert_eq_1(x, y):
    x_ptr = x
    y_ptr = y
    for i in unroll(0, 4):
        assert x_ptr[i] == y_ptr[i]
    for i in range(4, 8):
        assert x_ptr[i] == y_ptr[i]
    return


@inline
def assert_eq_2(x, y):
    x_ptr = x
    y_ptr = y
    for i in unroll(0, 4):
        assert x_ptr[i] == y_ptr[i]
    for i in range(4, 8):
        assert x_ptr[i] == y_ptr[i]
    return


@inline
def assert_eq_3(x, y):
    u = x + 7
    assert_eq_1(u - 7, y * 7 / 7)
    return


def assert_eq_4(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    dot_product_ee(x + 3, ONE_EF_PTR, y + 3)
    return


@inline
def assert_eq_5(x, y):
    dot_product_ee(x, ONE_EF_PTR, y)
    dot_product_ee(x + 3, ONE_EF_PTR, y + 3)
    return


@inline
def init_one_ef():
    one_ef = ONE_EF_PTR
    one_ef[0] = 1
    one_ef[1] = 0
    one_ef[2] = 0
    one_ef[3] = 0
    one_ef[4] = 0
    return
