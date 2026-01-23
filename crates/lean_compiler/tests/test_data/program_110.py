from snark_lib import *
def main():
    sum1: Mut = 0
    sum2: Mut = 0
    count: Mut = 0

    for i in unroll(0, 4):
        for j in unroll(0, 3):
            count = count + 1
            remainder = j % 2
            if remainder == 0:
                sum1 = sum1 + i + j
            else:
                sum2 = sum2 + i * j

    assert count == 12
    assert sum1 == 20
    assert sum2 == 6

    state: Mut = 0
    for phase in unroll(0, 5):
        match phase:
            case 0:
                state = state + 1
            case 1:
                state = state * 10
            case 2:
                if state == 10:
                    state = state + 5
                else:
                    state = state + 1000
            case 3:
                state = state * 2
            case 4:
                state = state + 1
    assert state == 31

    a: Mut = 5
    b: Mut = 10

    for round in unroll(0, 3):
        x, y = double_and_add(a, b)
        a = x
        b = y
    assert a == 40
    assert b == 25

    p: Mut = 1
    q: Mut = 2
    r: Mut = 3

    outer_sel = 1
    if outer_sel == 0:
        p = p + 100
    else if outer_sel == 1:
        inner_sel = 2
        match inner_sel:
            case 0:
                q = q + 200
            case 1:
                r = r + 300
            case 2:
                deep_cond = 0
                if deep_cond == 0:
                    p = p * 10
                    q = q * 10
                    r = r * 10
                else:
                    p = p + 9999
    else:
        r = r + 400

    assert p == 10
    assert q == 20
    assert r == 30

    result = complex_compute(3, 4, 5)
    assert result == 47

    fwd_val: Imu
    cond = 1
    if cond == 0:
        fwd_val = 100
    else:
        fwd_val = 200
    fwd_val2: Mut = fwd_val
    fwd_val2 = fwd_val2 + 50
    fwd_val2 = fwd_val2 * 2
    assert fwd_val2 == 500

    return

def double_and_add(x, y):
    return x * 2, y + 5

def complex_compute(a, b, c):
    sum = a + b
    product = sum * c
    extra = a * b
    return product + extra