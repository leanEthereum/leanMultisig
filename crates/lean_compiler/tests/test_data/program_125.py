from snark_lib import *


def main():
    r1 = cross_level_mut()
    assert r1 == 130

    a, b = loop_match_multi_mut()
    assert a == 9  # 1+3+5 = 9
    assert b == 6  # 2+4 = 6

    r2 = triple_same_mut()
    assert r2 == 492

    r3 = outer_used_after_inner()
    assert r3 == 45

    return


def cross_level_mut():
    total: Mut = 0
    for i in unroll(0, 5):
        local: Mut = i * 10
        for j in unroll(0, 3):
            local = local + j
            total = total + 1
        total = total + local
    return total


def loop_match_multi_mut():
    sum_a: Mut = 0
    sum_b: Mut = 0
    for i in unroll(0, 5):
        match i:
            case 0:
                sum_a = sum_a + 1
            case 1:
                sum_b = sum_b + 2
            case 2:
                sum_a = sum_a + 3
            case 3:
                sum_b = sum_b + 4
            case 4:
                sum_a = sum_a + 5
    return sum_a, sum_b


def triple_same_mut():
    x: Mut = 0
    for i in unroll(0, 3):
        x = x + i * 100
        for j in unroll(0, 4):
            x = x + j * 10
            for k in unroll(0, 2):
                x = x + k
    return x


def outer_used_after_inner():
    outer: Mut = 0
    for i in unroll(0, 5):
        for j in unroll(0, 3):
            outer = outer + i + j
    return outer
