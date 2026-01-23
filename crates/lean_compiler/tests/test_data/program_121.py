from snark_lib import *


def main():
    r1 = reuse_after_conditional(0)
    assert r1 == 15

    r2 = reuse_after_conditional(1)
    assert r2 == 35

    r3 = sequential_conditionals(0, 0)
    assert r3 == 5

    r4 = sequential_conditionals(1, 1)
    assert r4 == 36

    r5 = nested_read_write(0)
    assert r5 == 20

    r6 = nested_read_write(1)
    assert r6 == 40

    r7 = diamond_continue(0, 0)
    assert r7 == 222

    r8 = diamond_continue(1, 1)
    assert r8 == 484

    return


def reuse_after_conditional(cond):
    x: Mut = 10
    if cond == 1:
        x = x + 20  # x = 30
    result = x + 5  # 15 or 35
    return result


def sequential_conditionals(c1, c2):
    x: Mut = 5

    if c1 == 1:
        x = x + 10  # 15

    if c2 == 1:
        x = x * 2  # 10 or 30
        x = x + 6  # 16 or 36

    return x


def nested_read_write(cond):
    x: Mut = 10
    if cond == 0:
        y = x * 2  # Read x (10), compute 20
        x = y  # Write x = 20
    else:
        y = x * 3  # Read x (10), compute 30
        z = y + x  # Read both (30 + 10 = 40)
        x = z  # Write x = 40
    return x


def diamond_continue(c1, c2):
    x: Mut = 100
    if c1 == 0:
        x = x + 10  # 110
    else:
        x = x + 20  # 120
    x = x * 2  # 220 or 240

    if c2 == 0:
        x = x + 2  # 222 or 242
    else:
        x = x * 2  # 440 or 480
        x = x + 4  # 444 or 484

    return x
