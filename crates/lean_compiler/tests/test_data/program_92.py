from snark_lib import *


def main():
    x: Mut = 5
    cond = 1
    if cond == 1:
        x = compute(x, 3)
    else:
        x = compute(x, 10)
    assert x == 18
    return


def compute(a, b):
    return a * b + b
