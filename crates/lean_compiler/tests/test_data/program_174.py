from snark_lib import *

# Test classical match statement with cases starting after 0

def main():
    # Test 1: Basic match starting at 1
    r1 = match_start_at_1(2)
    assert r1 == 200

    # Test 2: First case of non-zero match
    r2 = match_start_at_1(1)
    assert r2 == 100

    # Test 3: Last case of non-zero match
    r3 = match_start_at_1(4)
    assert r3 == 400

    # Test 4: Match starting at 5
    r4 = match_start_at_5(7)
    assert r4 == 70

    # Test 5: Match starting at 10
    r5 = match_start_at_10(12)
    assert r5 == 1200

    # Test 6: Non-zero match with mutable variable
    r6 = match_nonzero_mutable(3)
    assert r6 == 330  # 300 + 30

    # Test 7: Nested non-zero matches
    r7 = nested_nonzero_match(2, 6)
    assert r7 == 260  # 200 + 60

    # Test 8: Non-zero match inside if
    r8 = nonzero_match_in_if(1, 3)
    assert r8 == 30

    return


def match_start_at_1(x):
    result: Imu
    match x:
        case 1:
            result = 100
        case 2:
            result = 200
        case 3:
            result = 300
        case 4:
            result = 400
    return result


def match_start_at_5(x):
    result: Imu
    match x:
        case 5:
            result = 50
        case 6:
            result = 60
        case 7:
            result = 70
        case 8:
            result = 80
    return result


def match_start_at_10(x):
    result: Imu
    match x:
        case 10:
            result = 1000
        case 11:
            result = 1100
        case 12:
            result = 1200
        case 13:
            result = 1300
    return result


def match_nonzero_mutable(x):
    result: Mut = 0
    match x:
        case 2:
            result = result + 200
        case 3:
            result = result + 300
        case 4:
            result = result + 400
    result = result + x * 10
    return result


def nested_nonzero_match(outer, inner):
    result: Imu
    match outer:
        case 1:
            match inner:
                case 5:
                    result = 150
                case 6:
                    result = 160
                case 7:
                    result = 170
        case 2:
            match inner:
                case 5:
                    result = 250
                case 6:
                    result = 260
                case 7:
                    result = 270
        case 3:
            match inner:
                case 5:
                    result = 350
                case 6:
                    result = 360
                case 7:
                    result = 370
    return result


def nonzero_match_in_if(cond, x):
    result: Imu
    if cond == 0:
        result = 0
    else:
        match x:
            case 2:
                result = 20
            case 3:
                result = 30
            case 4:
                result = 40
    return result
