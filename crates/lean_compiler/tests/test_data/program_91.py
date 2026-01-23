from snark_lib import *


def main():
    x: Mut = 1
    cond = 1
    if cond == 1:
        x = x + 1  # 2
        x = x * 2  # 4
        x = x + 3  # 7
        x = x * 2  # 14
        x = x + 1  # 15
    else:
        x = x + 100
    assert x == 15
    return
