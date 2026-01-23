from snark_lib import *
def main():
    assert test_func(0) == 10
    assert test_func(1) == 11
    assert test_func(2) == 12
    assert test_func(3) == 14
    assert test_func(4) == 18
    return

def test_func(sel):
    x: Mut = 10
    match sel:
        case 0:
        case 1:
            x = x + 1
        case 2:
            x = x + 1
            x = x + 1
        case 3:
            x = x + 1
            x = x + 1
            x = x + 2
        case 4:
            x = x + 1
            x = x + 1
            x = x + 2
            x = x + 4
    return x