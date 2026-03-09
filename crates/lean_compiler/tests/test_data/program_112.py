from snark_lib import *
def main():
    result1: Imu
    outer_sel = 1
    match outer_sel:
        case 0:
            result1 = 100
        case 1:
            inner_sel = 2
            match inner_sel:
                case 0:
                    result1 = 200
                case 1:
                    result1 = 300
                case 2:
                    result1 = 456
    assert result1 == 456

    counter: Imu
    flag: Imu

    phase = 1
    if phase == 0:
        counter = 0
        flag = 100
    elif phase == 1:
        counter = 10
        flag = 200
    else:
        counter = 100
        flag = 300

    counter2: Mut = counter
    flag2: Mut = flag
    counter2 = counter2 + 5
    flag2 = flag2 * 2

    assert counter2 == 15
    assert flag2 == 400

    x: Imu
    y: Imu

    init_sel = 0
    if init_sel == 0:
        x = 5
        y = 10
    else:
        x = 50
        y = 100

    x2: Mut = x
    y2: Mut = y
    x2 = x2 * 2
    y2 = y2 + x2
    x2 = x2 + 1
    x2 = x2 * y2

    assert x2 == 220
    assert y2 == 20

    outcome: Imu
    selector = 4
    match selector:
        case 0:
            outcome = compute_outcome(0, 0)
        case 1:
            outcome = compute_outcome(1, 1)
        case 2:
            outcome = compute_outcome(2, 4)
        case 3:
            outcome = compute_outcome(3, 9)
        case 4:
            outcome = compute_outcome(4, 16)
        case 5:
            outcome = compute_outcome(5, 25)
    assert outcome == 84

    p: Imu
    q: Imu
    r: Imu

    s1 = 1
    if s1 == 1:
        p = 1
    else:
        p = 10

    s2 = 0
    if s2 == 1:
        q = 100
    else:
        q = p + 10

    s3 = 1
    if s3 == 1:
        r = p + q + 100
    else:
        r = 999

    assert p == 1
    assert q == 11
    assert r == 112

    return

def compute_outcome(a, b):
    return a * b + a + b