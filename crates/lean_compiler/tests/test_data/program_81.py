from snark_lib import *
def main():
    assert test_func(0) == 11
    assert test_func(1) == 10  # no mutation
    assert test_func(2) == 30
    return

def test_func(sel):
    x: Mut = 10
    match sel:
        case 0:
            x = x + 1
        case 1:
        case 2:
            x = x + 20
    return x