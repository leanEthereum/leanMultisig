from snark_lib import *


def main():
    x = Array(2)
    x[0] = 3
    x[1] = 5
    for i in unroll(0, 2):
        for j in range(0, x[i]):
            print(i, j)
    return
