from snark_lib import *

N = 5


def main():
    arr = Array(N)

    sum: Mut = 0
    for i in unroll(0, N):
        arr[i] = i * 2
        sum = sum + arr[i]
    assert sum == 20

    product: Mut = 1
    for i in unroll(1, N):
        product = product * arr[i]
    assert product == 384
    return
