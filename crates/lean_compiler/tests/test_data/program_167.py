from snark_lib import *

ARR = [1, 2, 3, 4, 5]


def main():
    x = (len(ARR) + ARR[2]) / ARR[3]
    sum: Mut = 0
    for i in range(0, x):
        sum += 1
    assert sum == 2
    return
