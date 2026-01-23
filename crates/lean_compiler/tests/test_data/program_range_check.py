from snark_lib import *


def main():
    # Test range check with various values
    x = 500
    assert x < 1000

    y = 0
    assert y < 10

    z = 999
    assert z < 1000

    # Test with computed value
    a = 100 + 200
    assert a < 400

    # Test <= (becomes < bound+1)
    b = 999
    assert b <= 999

    c = 0
    assert c <= 0

    # Test with non-constant bound
    bound = 500
    d = 100
    assert d < bound

    # Test with computed bound
    e = 50
    f = 200 + 100  # f = 300
    assert e < f

    for i in range(50, 100):
        for j in range(i - 10, i + 1):
            assert j <= i

    return
