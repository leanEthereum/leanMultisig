from snark_lib import *
def main():
    assert test_func(0) == 11
    assert test_func(1) == 20
    assert test_func(2) == 30
    return

def test_func(cond):
    x: Mut = 10
    if cond == 0:
        x = x + 1
    else if cond == 1:
        x = x + 10
    else:
        x = x + 20
    return x