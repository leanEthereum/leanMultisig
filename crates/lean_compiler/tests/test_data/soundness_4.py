from snark_lib import *


def main():
    p = 0
    n = p[0]
    expected_sum_pos = p[1]
    expected_sum_neg = p[2]
    x = p[3]
    y = p[4]
    expected_pipeline = p[5]
    threshold = p[6]
    threshold_check = p[7]

    assert n == 5

    markers = Array(5)
    for i in unroll(0, 5):
        markers[i] = i

    sum_pos: Mut = 0
    sum_neg: Mut = 0
    for i in range(0, 5):
        m = markers[i]
        if m == 0:
            sum_neg = sum_neg + 10
        else:
            sum_pos = sum_pos + m
    assert sum_pos == expected_sum_pos
    assert sum_neg == expected_sum_neg

    assert pipeline(x, y) == expected_pipeline

    if threshold_check == 1:
        assert threshold < 50
    else:
        assert threshold == 0

    assert threshold_check * (1 - threshold_check) == 0
    return


@inline
def pipeline(a, b):
    return wrapper(a, b) + a


def wrapper(a, b):
    return inner(a, b) + b


@inline
def inner(a, b):
    return a * b
