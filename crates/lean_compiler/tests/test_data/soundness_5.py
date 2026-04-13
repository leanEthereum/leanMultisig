from snark_lib import *


def main():
    p = 0
    seed = p[0]
    n = p[1]
    last_write = p[2]
    match_tally = p[3]
    pipeline_squared = p[4]
    paired = p[5]
    flag = p[6]
    alt = p[7]

    assert n == 4

    counter: Mut = 0
    for i in range(0, 4):
        counter = 2 * i + 1
    assert counter == last_write

    acc: Mut = seed
    for i in range(0, 4):
        match i:
            case 0:
                acc = acc + 1
            case 1:
                acc = acc + 3
            case 2:
                acc = acc + 5
            case 3:
                acc = acc + 7
    assert acc == match_tally

    assert sqr_via_pipeline(seed + n) == pipeline_squared

    assert paired_sum(seed, n) == paired

    chosen: Imu
    if flag == 1:
        chosen = seed
    else:
        chosen = seed * 2
    assert chosen == alt

    assert flag * (1 - flag) == 0
    return


@inline
def sqr_via_pipeline(x):
    return mul_boxed(x, x)


def mul_boxed(a, b):
    return a * b


def paired_sum(a, b):
    total: Mut = 0
    for i in range(0, 4):
        total = total + a + b
    return total
