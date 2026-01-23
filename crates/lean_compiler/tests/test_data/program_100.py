from snark_lib import *


def main():
    x: Imu
    y: Imu

    cond = 1
    if cond == 1:
        x = 10
        y = 20
    else:
        x = 100
        y = 200

    x2: Mut = x
    y2: Mut = y
    x2 = x2 + y2  # 10 + 20 = 30
    y2 = y2 - 5  # 20 - 5 = 15

    assert x2 == 30
    assert y2 == 15
    return
