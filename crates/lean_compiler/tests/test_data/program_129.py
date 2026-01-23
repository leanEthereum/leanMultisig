from snark_lib import *


def main():
    x: Mut = Array(1)
    x[0] = 1
    for i in unroll(0, 5):
        y = Array(1)
        y[0] = x[0] + 1
        x = y
    assert x[0] == 6
    return
