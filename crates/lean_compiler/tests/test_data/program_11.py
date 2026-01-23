from snark_lib import *

ARR = [0, 1, 2, 3, 4]


def main():
    vector = DynArray([])
    for i in unroll(0, len(ARR)):
        k = ARR[i]
        vector.push(DynArray([]))
        vector[k].push(k)
        assert vector[k][0] == k
    return
