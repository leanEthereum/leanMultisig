from snark_lib import *


def main():
    selector = 2
    match selector:
        case 0:
            result: Mut = 1
            assert result == 1
        case 1:
            result: Mut = 10
            assert result == 10
        case 2:
            result: Mut = 100
            result = result + 5
            assert result == 105
    return
