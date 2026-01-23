from snark_lib import *
def main():
    r1 = partial_match_update(0)
    assert r1 == 100

    r2 = partial_match_update(1)
    assert r2 == 10

    r3 = partial_match_update(2)
    assert r3 == 200

    a1, b1, c1 = scattered_updates(0)
    assert a1 == 1
    assert b1 == 0
    assert c1 == 0

    a2, b2, c2 = scattered_updates(1)
    assert a2 == 0
    assert b2 == 2
    assert c2 == 0

    a3, b3, c3 = scattered_updates(2)
    assert a3 == 0
    assert b3 == 0
    assert c3 == 3

    r4 = sandwich_phi(0)
    assert r4 == 60

    r5 = sandwich_phi(1)
    assert r5 == 80

    r6 = loop_partial_match()
    assert r6 == 10  # 1+2+3+4

    return

def partial_match_update(selector):
    x: Mut = 10
    match selector:
        case 0:
            x = 100  # Modified
        case 1:
        case 2:
            x = 200  # Modified
    return x

def scattered_updates(selector):
    a: Mut = 0
    b: Mut = 0
    c: Mut = 0
    match selector:
        case 0:
            a = 1
        case 1:
            b = 2
        case 2:
            c = 3
    return a, b, c

def sandwich_phi(cond):
    x: Mut = 10
    x = x * 2  # Pre-branch: x = 20

    if cond == 0:
        x = x + 10  # 30
    else:
        x = x + 20  # 40

    x = x * 2  # Post-branch: 60 or 80
    return x

def loop_partial_match():
    sum: Mut = 0
    for i in unroll(0, 4):
        match i:
            case 0:
                sum = sum + 1
            case 1:
                sum = sum + 2
            case 2:
                sum = sum + 3
            case 3:
                sum = sum + 4
    return sum