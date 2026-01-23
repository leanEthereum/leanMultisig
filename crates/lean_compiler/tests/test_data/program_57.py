from snark_lib import *


def main():
    x: Mut = 1
    x = step1(x)
    x = step2(x)
    x = step3(x)
    assert x == 47
    return


def step1(n: Mut):
    n = n * 2
    n = n + 1
    return n


def step2(n: Mut):
    n = n * 3
    n = n + 2
    return n


def step3(n: Mut):
    n = n * 4
    n = n + 3
    return n
