from snark_lib import *


def main():
    assert compute(0, 0, 0) == 1008
    assert compute(0, 0, 1) == 1009
    assert compute(0, 1, 0) == 1012
    assert compute(0, 1, 1) == 1013
    assert compute(1, 0, 0) == 1036
    assert compute(1, 0, 1) == 1037
    assert compute(1, 1, 0) == 1046
    assert compute(1, 1, 1) == 1047
    return


def compute(a, b, c):
    base = 1000
    outer_val: Imu
    mid_val: Imu
    inner_val: Imu

    match a:
        case 0:
            outer_val = 5
            local_a: Imu
            local_a = a + outer_val

            match b:
                case 0:
                    mid_val = 3
                    local_b: Imu
                    local_b = local_a + mid_val

                    match c:
                        case 0:
                            inner_val = base + local_b + c
                        case 1:
                            inner_val = base + local_b + c
                case 1:
                    mid_val = 7
                    local_b: Imu
                    local_b = local_a + mid_val

                    match c:
                        case 0:
                            inner_val = base + local_b + c
                        case 1:
                            inner_val = base + local_b + c
        case 1:
            outer_val = 15
            local_a: Imu
            local_a = a + outer_val

            match b:
                case 0:
                    mid_val = 20
                    local_b: Imu
                    local_b = local_a + mid_val

                    match c:
                        case 0:
                            inner_val = base + local_b + c
                        case 1:
                            inner_val = base + local_b + c
                case 1:
                    mid_val = 30
                    local_b: Imu
                    local_b = local_a + mid_val

                    match c:
                        case 0:
                            inner_val = base + local_b + c
                        case 1:
                            inner_val = base + local_b + c

    return inner_val
