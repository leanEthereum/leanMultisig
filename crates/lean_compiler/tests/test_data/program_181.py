from snark_lib import *

# Comprehensive test for compile-time 'or' conditions

FIVE = 5
TEN = 10


def main():
    result: Mut = 0

    arr3 = DynArray([1, 2, 3])
    arr0 = DynArray([])
    nested = DynArray([DynArray([10, 20]), DynArray([30])])

    # --- Basic truth table ---

    # true or true
    if 10 == 10 or 20 == 20:
        result = result + 1

    # true or false
    if 10 == 10 or 20 == 999:
        result = result + 2

    # false or true
    if 10 == 999 or 20 == 20:
        result = result + 4

    # false or false => excluded
    if 10 == 999 or 20 == 999:
        result = result + 100000

    # --- or with else ---

    if 10 == 999 or 30 == 30:
        result = result + 8
    else:
        result = result + 100000

    if 10 == 999 or 20 == 999:
        result = result + 100000
    else:
        result = result + 16

    # --- Chained or ---

    if 1 == 0 or 2 == 0 or 3 == 3:
        result = result + 32

    if 1 == 0 or 2 == 0 or 3 == 0:
        result = result + 100000

    # --- or with != and < ---

    if 10 != 10 or 20 != 999:
        result = result + 64

    if 10 != 10 or 20 != 20:
        result = result + 100000

    if 5 < 3 or 3 < 5:
        result = result + 128

    # --- or with len() on DynArrays ---

    if len(arr3) == 3 or len(arr0) == 99:
        result = result + 256

    if len(arr0) != 0 or len(arr3) != 0:
        result = result + 512

    if len(arr0) != 0 or len(arr0) == 99:
        result = result + 100000

    # --- or with nested DynArray len() ---

    if len(nested[0]) == 2 or len(nested[1]) == 99:
        result = result + 1024

    if len(nested[0]) == 99 or len(nested[1]) == 1:
        result = result + 2048

    # --- or with constants ---

    if FIVE == 5 or TEN == 99:
        result = result + 4096

    if FIVE == 99 or TEN == 99:
        result = result + 100000

    # --- or inside unrolled loop ---

    for i in unroll(0, 4):
        if i == 1 or i == 3:
            result = result + 8192

    # --- or with len() in unrolled loop over nested ---

    for i in unroll(0, len(nested)):
        if len(nested[i]) == 2 or len(nested[i]) == 1:
            result = result + 16384

    # --- Nested or: if-or inside if-or ---

    if 1 == 1 or 2 == 99:
        if 3 == 99 or 4 == 4:
            result = result + 32768

    # false outer kills inner
    if 1 == 99 or 2 == 99:
        if 3 == 3 or 4 == 4:
            result = result + 100000

    # --- or with elif ---

    if 1 == 99 or 2 == 99:
        result = result + 100000
    elif 3 == 99 or 4 == 4:
        result = result + 65536
    else:
        result = result + 100000

    # elif-or: first branch true
    if 1 == 1 or 2 == 99:
        result = result + 131072
    elif 3 == 3 or 4 == 4:
        result = result + 100000

    # elif-or: all false => else
    val: Imu
    if 1 == 99 or 2 == 99:
        val = 100000
    elif 3 == 99 or 4 == 99:
        val = 100000
    else:
        val = 262144
    result = result + val

    # --- or inside @inline function ---

    result = result + or_in_inline(arr3)

    # --- or gating mutation ---

    x: Mut = 0
    if 1 == 1 or 2 == 99:
        x = 42
    assert x == 42

    y: Mut = 99
    if 1 == 99 or 2 == 99:
        y = 0
    assert y == 99

    # --- or gating a loop ---

    counter: Mut = 0
    if len(arr3) == 3 or len(arr0) != 0:
        for i in unroll(0, len(arr3)):
            counter = counter + arr3[i]
    assert counter == 6

    # --- or inside nested unrolled loops ---

    grid_sum: Mut = 0
    for i in unroll(0, len(nested)):
        for j in unroll(0, len(nested[i])):
            if i == 0 or j == 0:
                grid_sum = grid_sum + nested[i][j]
    # nested = [[10, 20], [30]]
    # (0,0): i==0 true  => +10
    # (0,1): i==0 true  => +20
    # (1,0): j==0 true  => +30
    assert grid_sum == 60

    result = result + 1048576

    # --- or with DynArray push/pop ---

    arr = DynArray([1, 2])
    arr.push(3)
    if len(arr) == 3 or len(arr) == 2:
        result = result + 2097152

    arr.pop()
    if len(arr) == 3 or len(arr) == 2:
        result = result + 4194304

    if len(arr) == 3 or len(arr) == 99:
        result = result + 100000

    # expected:
    #   1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 + 256 + 512
    # + 1024 + 2048 + 4096 + 8192*2 + 16384*2 + 32768
    # + 65536 + 131072 + 262144 + 524288 + 1048576
    # + 2097152 + 4194304
    assert result == expected_result()
    return


@inline
def or_in_inline(arr):
    out: Mut = 0
    if len(arr) == 3 or len(arr) == 0:
        out = out + 524288
    if len(arr) == 99 or len(arr) == 98:
        out = out + 100000
    for i in unroll(0, len(arr)):
        if i == 0 or i == 2:
            out = out + 0
    return out


@inline
def expected_result():
    return 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 + 256 + 512 + 1024 + 2048 + 4096 + 8192 + 8192 + 16384 + 16384 + 32768 + 65536 + 131072 + 262144 + 524288 + 1048576 + 2097152 + 4194304
