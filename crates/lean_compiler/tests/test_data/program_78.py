from snark_lib import *


def main():
    x: Mut = 5
    x = x + x  # Should be 5 + 5 = 10, not 10 + 10
    assert x == 10

    x = x * x  # 10 * 10 = 100
    assert x == 100
    return
