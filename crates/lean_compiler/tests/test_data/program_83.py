from snark_lib import *


def main():
    x: Imu
    cond = 1
    if cond == 1:
        x = 10
    else:
        x = 20
    x2: Mut = x
    x2 = x2 + 1
    assert x2 == 11
    return
