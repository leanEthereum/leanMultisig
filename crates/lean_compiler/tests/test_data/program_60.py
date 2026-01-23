from snark_lib import *

N = 6


def main():
    factorial: Mut = 1
    for i in unroll(1, N):
        factorial = factorial * i
    assert factorial == 120

    sum_squares: Mut = 0
    for i in unroll(1, N):
        sum_squares = sum_squares + i * i
    assert sum_squares == 55

    triangular: Mut = 0
    for i in unroll(1, N):
        triangular = triangular + i
    assert triangular == 15
    return
