from snark_lib import *

DIM = 5


def main():
    v = DynArray([1, 2, 3])
    sum1: Mut = 0
    for i in unroll(0, len(v)):
        sum1 = sum1 + v[i]
    assert sum1 == 6
    v.push(4)
    assert len(v) == 4
    sum2: Mut = 0
    for i in unroll(0, len(v)):
        sum2 = sum2 + v[i]
    assert sum2 == 10
    # Test nested vectors with len(w[i])
    w = DynArray([])
    for i in unroll(0, 5):
        w.push(DynArray([]))
        for j in unroll(0, i):
            w[i].push(1)
        assert len(w[i]) == i
    assert len(w) == 5
    a = Array(DIM)
    for i in unroll(0, DIM):
        a[i] = 1
    w.push(DynArray([a]))
    b = Array(DIM)
    copy_5(w[5][0], b)
    return


@inline
def copy_5(a, b):
    dot_product_ee(a, ONE_EF_PTR, b)
    return
