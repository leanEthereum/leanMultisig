from snark_lib import *
# Test: Match statement inside non-unrolled loop with mutable variables


def main():
    score: Mut = 0
    for i in range(0, 4):
        match i:
            case 0:
                score += 100
            case 1:
                score += 50
            case 2:
                score += 25
            case 3:
                score += 10
    # i=0: score=100
    # i=1: score=150
    # i=2: score=175
    # i=3: score=185
    assert score == 185
    return
