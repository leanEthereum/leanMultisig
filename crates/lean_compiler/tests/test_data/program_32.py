from snark_lib import *


def main():
    res = fib(8)
    assert res == 21
    return


def fib(n: Const):
    if n == 0:
        return 0
    if n == 1:
        return 1
    a = fib(saturating_sub(n, 1))
    b = fib(saturating_sub(n, 2))
    return a + b
