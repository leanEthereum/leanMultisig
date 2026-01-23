from snark_lib import *


def main():
    x: Mut = 10
    y = 5  # immutable

    cond = 1
    if cond == 1:
        x = x + y  # 10 + 5 = 15
        z = x + y  # 15 + 5 = 20, immutable
        x = x + z  # 15 + 20 = 35
    else:
        x = x + 100

    assert x == 35
    return
