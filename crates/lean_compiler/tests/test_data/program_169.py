from snark_lib import *


def main():
    x = 1 + 2 + 3
    assert x == 6

    y = foo(10, 20, 30)
    assert y == 60
    return


def foo(a, b, c):
    return a + b + c
