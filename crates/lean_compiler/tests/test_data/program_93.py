from snark_lib import *


def main():
    outer_x: Mut = 0
    for i in unroll(0, 2):
        x: Mut = 1  # fresh x each iteration
        x = x + i
        outer_x = outer_x + x
    assert outer_x == 3
    return
