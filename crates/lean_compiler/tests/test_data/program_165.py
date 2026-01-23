from snark_lib import *
# Comprehensive test: nested unrolled loops, vectors with pushes in various scopes


def main():
    # === PART 1: Basic nested loops over 2D vector ===

    outer = DynArray([DynArray([1, 2]), DynArray([10, 20, 30])])

    total: Mut = 0
    for i in unroll(0, len(outer)):
        row_sum: Mut = 0
        for j in unroll(0, len(outer[i])):
            row_sum = row_sum + outer[i][j]
        total = total + row_sum
    assert total == 63

    # === PART 2: Push new row to outer, iterate again ===

    outer.push(DynArray([100, 200]))
    assert len(outer) == 3

    total: Mut = 0
    for i in unroll(0, len(outer)):
        row_sum: Mut = 0
        for j in unroll(0, len(outer[i])):
            row_sum = row_sum + outer[i][j]
        total = total + row_sum
    assert total == 363

    # === PART 3: Multiple vectors cross product ===

    v1 = DynArray([1, 2, 3])
    v2 = DynArray([10, 20])

    cross_sum: Mut = 0
    for i in unroll(0, len(v1)):
        for j in unroll(0, len(v2)):
            cross_sum = cross_sum + v1[i] * v2[j]
    assert cross_sum == 180

    v2.push(30)
    cross_sum: Mut = 0
    for i in unroll(0, len(v1)):
        for j in unroll(0, len(v2)):
            cross_sum = cross_sum + v1[i] * v2[j]
    assert cross_sum == 360

    # === PART 4: Accumulator reused without reset ===

    data = DynArray([5, 10, 15, 20])

    acc: Mut = 0
    for i in unroll(0, len(data)):
        acc = acc + data[i]
    assert acc == 50

    for i in unroll(0, len(data)):
        acc = acc + data[i] * data[i]
    assert acc == 800

    # === PART 5: if inside unrolled loop (compile-time condition) ===

    data2 = DynArray([1, 2, 3, 4])
    acc2: Mut = 0
    for i in unroll(0, len(data2)):
        acc2 = acc2 + data2[i]
        if i == 2:
            acc2 = acc2 * 2
    assert acc2 == 16

    assert inlined() == 5

    return


def inlined():
    v = DynArray([1, 2, 3])
    sum: Mut = 0
    for i in unroll(0, len(v)):
        sum = sum + v[i]
    debug_assert(sum == 6)
    v.push(4)
    assert len(v) == 4
    sum: Mut = 0
    for i in unroll(0, len(v)):
        sum += v[i]
    assert sum == 10
    w = DynArray([])
    for i in unroll(0, 5):
        w.push(DynArray([]))
        for j in unroll(0, i):
            w[i].push(1)
        sum: Mut = 0
        for j in unroll(0, len(w[i])):
            sum += w[i][j]
        assert sum == i
    return len(w)
