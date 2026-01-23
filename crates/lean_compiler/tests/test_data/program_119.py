from snark_lib import *


def main():
    assert five_way(0) == 1
    assert five_way(1) == 2
    assert five_way(2) == 4
    assert five_way(3) == 8
    assert five_way(4) == 16

    a0, b0, c0 = five_way_multi(0)
    assert a0 == 1
    assert b0 == 0
    assert c0 == 0

    a2, b2, c2 = five_way_multi(2)
    assert a2 == 0
    assert b2 == 0
    assert c2 == 4

    a4, b4, c4 = five_way_multi(4)
    assert a4 == 0
    assert b4 == 16
    assert c4 == 0

    result = five_way_postmerge(2)
    assert result == 24  # 4 * 6

    result2 = nested_five_way(1, 2)
    assert result2 == 1020

    return


def five_way(n):
    x: Mut = 0
    match n:
        case 0:
            x = 1
        case 1:
            x = 2
        case 2:
            x = 4
        case 3:
            x = 8
        case 4:
            x = 16
    return x


def five_way_multi(n):
    a: Mut = 0
    b: Mut = 0
    c: Mut = 0
    match n:
        case 0:
            a = 1
        case 1:
            b = 2
        case 2:
            c = 4
        case 3:
            a = 8
        case 4:
            b = 16
    return a, b, c


def five_way_postmerge(n):
    x: Mut = 0
    match n:
        case 0:
            x = 1
        case 1:
            x = 2
        case 2:
            x = 4
        case 3:
            x = 8
        case 4:
            x = 16
    result = x * 6
    return result


def nested_five_way(outer, inner):
    x: Mut = 1000
    match outer:
        case 0:
            match inner:
                case 0:
                    x = x + 1
                case 1:
                    x = x + 2
                case 2:
                    x = x + 3
                case 3:
                    x = x + 4
                case 4:
                    x = x + 5
        case 1:
            match inner:
                case 0:
                    x = x + 10
                case 1:
                    x = x + 20
                case 2:
                    x = x + 20
                case 3:
                    x = x + 30
                case 4:
                    x = x + 40
        case 2:
            match inner:
                case 0:
                    x = x + 100
                case 1:
                    x = x + 200
                case 2:
                    x = x + 300
                case 3:
                    x = x + 400
                case 4:
                    x = x + 500
    return x
