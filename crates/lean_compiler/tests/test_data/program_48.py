from snark_lib import *

N = 5
M = 3


def main():
    acc: Mut = 0
    for i in unroll(0, N):
        acc = acc + M
    assert acc == 15

    product: Mut = 1
    for i in unroll(0, M):
        product = product * 2
    assert product == 8
    return
