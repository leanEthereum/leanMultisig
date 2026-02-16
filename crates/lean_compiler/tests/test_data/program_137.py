from snark_lib import *
# Test: Deeply nested conditionals inside non-unrolled loop

def main():
    result: Mut = 0
    for i in range(0, 6):
        if i == 0:
            result += 1
        elif i == 1:
            result += 2
        elif i == 2:
            result += 4
        elif i == 3:
            result += 8
        elif i == 4:
            result += 16
        else:
            result += 32
    # Powers of 2: 1 + 2 + 4 + 8 + 16 + 32 = 63
    assert result == 63
    return