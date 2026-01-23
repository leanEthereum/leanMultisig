from snark_lib import *

ARR = [[1], [7, 3], [7]]
N = 2 + len(ARR[0])


def main():
    for i in unroll(0, N):
        for j in unroll(0, len(ARR[i])):
            assert j * (j - 1) == 0
    return
