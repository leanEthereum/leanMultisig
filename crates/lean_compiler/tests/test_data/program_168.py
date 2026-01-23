from snark_lib import *
# Comprehensive test for vector.pop()


def main():
    # Basic pop on simple vector
    v1 = DynArray([1, 2, 3, 4, 5])
    assert len(v1) == 5
    v1.pop()
    assert len(v1) == 4
    v1.pop()
    v1.pop()
    assert len(v1) == 2
    # v1 should now be [1, 2]
    assert v1[0] == 1
    assert v1[1] == 2

    """
    multi line
    comment
    """

    # Pop in unrolled loop
    v2 = DynArray([10, 20, 30, 40, 50])
    for i in unroll(0, 3):
        v2.pop()
    assert len(v2) == 2
    assert v2[0] == 10
    assert v2[1] == 20

    # Pop from nested vector
    matrix = DynArray([DynArray([1, 2, 3]), DynArray([4, 5, 6, 7]), DynArray([8, 9])])
    assert len(matrix[0]) == 3
    assert len(matrix[1]) == 4
    matrix[1].pop()
    assert len(matrix[1]) == 3
    matrix[0].pop()
    matrix[0].pop()
    assert len(matrix[0]) == 1
    assert matrix[0][0] == 1
    assert matrix[1][0] == 4
    assert matrix[1][1] == 5
    assert matrix[1][2] == 6

    # Pop outer vector element
    matrix.pop()
    assert len(matrix) == 2

    # Mix push and pop
    v3 = DynArray([100])
    v3.push(200)
    v3.push(300)
    assert len(v3) == 3
    v3.pop()
    assert len(v3) == 2
    v3.push(400)
    assert len(v3) == 3
    assert v3[0] == 100
    assert v3[1] == 200
    assert v3[2] == 400

    # Pop until one element remains
    v4 = DynArray([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
    for i in unroll(0, 9):
        v4.pop()
    assert len(v4) == 1
    assert v4[0] == 1

    # Pop on nested vector with index expression
    nested = DynArray([DynArray([DynArray([1, 2, 3])])])
    nested[0][0].pop()
    assert len(nested[0][0]) == 2

    # Build vector, pop some, then iterate
    v5 = DynArray([])
    for i in unroll(0, 5):
        v5.push(i * 10)
    v5.pop()
    v5.pop()
    sum: Mut = 0
    for i in unroll(0, len(v5)):
        sum = sum + v5[i]
    # v5 = [0, 10, 20], sum = 30
    assert sum == 30

    return
