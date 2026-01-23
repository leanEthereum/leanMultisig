from snark_lib import *
# Comprehensive tests for mutable variables with early exits (panic/return) in branches.
# This tests the SSA transformation when branches end with assert False or return.
# Bug fix: ensure proper handling of mutable variable unification when some branches exit early.

def main():
    # ==========================================================================
    # TEST 1: Basic - panic in else branch (the original bug case)
    # ==========================================================================
    two: Imu
    if 1 == 1:
        two = 2
    else:
        assert False
    assert two == 2

    # ==========================================================================
    # TEST 2: panic in then branch
    # ==========================================================================
    three: Imu
    if 1 != 1:
        assert False
    else:
        three = 3
    assert three == 3

    # ==========================================================================
    # TEST 3: Multiple mutable variables, panic in else
    # ==========================================================================
    a: Imu
    b: Imu
    c: Imu
    if 1 == 1:
        a = 10
        b = 20
        c = 30
    else:
        assert False
    assert a == 10
    assert b == 20
    assert c == 30

    # ==========================================================================
    # TEST 4: Nested if with panic in inner else
    # ==========================================================================
    x: Imu
    if 1 == 1:
        if 2 == 2:
            x = 42
        else:
            assert False
    else:
        assert False
    assert x == 42

    # ==========================================================================
    # TEST 5: Mutable modified = None in then, panic in else
    # ==========================================================================
    counter: Mut = 0
    if 1 == 1:
        counter = counter + 5
    else:
        assert False
    assert counter == 5

    # ==========================================================================
    # TEST 6: Multiple modifications before panic check
    # ==========================================================================
    val: Mut = 1
    val = val * 2
    val = val + 3
    if val == 5:
        val = val * 10
    else:
        assert False
    assert val == 50

    # ==========================================================================
    # TEST 7: Chain of else-if with panic in final else
    # ==========================================================================
    result: Imu
    selector = 1
    if selector == 0:
        result = 100
    else if selector == 1:
        result = 200
    else if selector == 2:
        result = 300
    else:
        assert False
    assert result == 200

    # ==========================================================================
    # TEST 8: Match with panic in one arm
    # ==========================================================================
    matched: Imu
    tag = 1
    match tag:
        case 0:
            assert False
        case 1:
            matched = 111
        case 2:
            assert False
    assert matched == 111

    # ==========================================================================
    # TEST 9: Match where only one arm doesn't panic
    # ==========================================================================
    only_valid: Imu
    tag2 = 2
    match tag2:
        case 0:
            assert False
        case 1:
            assert False
        case 2:
            only_valid = 222
        case 3:
            assert False
    assert only_valid == 222

    # ==========================================================================
    # TEST 10: Panic in deeply nested structure
    # ==========================================================================
    deep: Imu
    if 1 == 1:
        if 1 == 1:
            if 1 == 1:
                deep = 999
            else:
                assert False
        else:
            assert False
    else:
        assert False
    assert deep == 999

    # ==========================================================================
    # TEST 11: Mutable used = None after branch with panic
    # ==========================================================================
    acc: Mut = 0
    for i in unroll(0, 3):
        if 1 == 1:
            acc = acc + i
        else:
            assert False
    assert acc == 3

    # ==========================================================================
    # TEST 12: Forward declared with = None panic in branch
    # ==========================================================================
    fwd: Imu
    cond = 1
    if cond == 1:
        fwd = 777
    else:
        assert False
    assert fwd == 777

    # ==========================================================================
    # TEST 13: Both mutable and immutable forward decl with panic
    # ==========================================================================
    imm: Imu
    mtbl: Imu
    flag = 0
    if flag == 0:
        imm = 100
        mtbl = 200
    else:
        assert False
    mtbl2: Mut = mtbl
    mtbl2 = mtbl2 + 50
    assert imm == 100
    assert mtbl2 == 250

    # ==========================================================================
    # TEST 14: Return in function branch (early exit)
    # ==========================================================================
    res14 = test_early_return(1)
    assert res14 == 10
    res14b = test_early_return(0)
    assert res14b == 20

    # ==========================================================================
    # TEST 15: Multiple mutable vars with return in branch
    # ==========================================================================
    r15a, r15b = test_multi_return(1)
    assert r15a == 100
    assert r15b == 200

    # ==========================================================================
    # TEST 16: Mutable with = None panic in match, then more operations
    # ==========================================================================
    m16: Mut = 5
    sel16 = 0
    match sel16:
        case 0:
            m16 = m16 * 2
        case 1:
            assert False
    m16 = m16 + 3
    assert m16 == 13

    # ==========================================================================
    # TEST 17: Nested match with panic
    # ==========================================================================
    nested_match: Imu
    outer = 1
    match outer:
        case 0:
            assert False
        case 1:
            inner = 0
            match inner:
                case 0:
                    nested_match = 500
                case 1:
                    assert False
    assert nested_match == 500

    # ==========================================================================
    # TEST 18: If inside match with panic
    # ==========================================================================
    if_in_match: Imu
    m18_sel = 0
    match m18_sel:
        case 0:
            cond18 = 1
            if cond18 == 1:
                if_in_match = 600
            else:
                assert False
        case 1:
            assert False
    assert if_in_match == 600

    # ==========================================================================
    # TEST 19: Match inside if with panic
    # ==========================================================================
    match_in_if: Imu
    cond19 = 1
    if cond19 == 1:
        tag19 = 1
        match tag19:
            case 0:
                assert False
            case 1:
                match_in_if = 700
    else:
        assert False
    assert match_in_if == 700

    # ==========================================================================
    # TEST 20: Panic after partial assignment
    # ==========================================================================
    partial: Imu
    check = 0
    if check == 0:
        partial_tmp: Mut = 1
        partial_tmp = partial_tmp + 1
        partial_tmp = partial_tmp * 2
        partial = partial_tmp
    else:
        partial = 999
        assert False
    assert partial == 4

    # ==========================================================================
    # TEST 21: Unrolled loop with panic in branch at each iteration
    # ==========================================================================
    sum21: Mut = 0
    for i in unroll(0, 5):
        expected = i
        if i == expected:
            sum21 = sum21 + i
        else:
            assert False
    assert sum21 == 10

    # ==========================================================================
    # TEST 22: Function with mutable param and early return
    # ==========================================================================
    res22 = func_with_mut_param(5, 1)
    assert res22 == 50

    # ==========================================================================
    # TEST 23: Multiple levels - if/match/if with panics
    # ==========================================================================
    multi_level: Imu
    c1 = 1
    if c1 == 1:
        s1 = 0
        match s1:
            case 0:
                c2 = 0
                if c2 == 0:
                    multi_level = 888
                else:
                    assert False
            case 1:
                assert False
    else:
        assert False
    assert multi_level == 888

    # ==========================================================================
    # TEST 24: Panic in both outer branches but inner assigns
    # ==========================================================================
    inner_assigns: Imu
    outer24 = 0
    match outer24:
        case 0:
            inner24 = 1
            if inner24 == 1:
                inner_assigns = 1000
            else:
                assert False
        case 1:
            assert False
    assert inner_assigns == 1000

    # ==========================================================================
    # TEST 25: Complex - multiple vars, nested, with panics
    # ==========================================================================
    va: Imu
    vb: Imu
    vc: Imu

    outer25 = 1
    if outer25 == 1:
        va = 1
        mid25 = 0
        match mid25:
            case 0:
                vb = 2
                inner25 = 1
                if inner25 == 1:
                    vc = 3
                else:
                    assert False
            case 1:
                assert False
    else:
        assert False

    total = va + vb + vc
    assert total == 6

    return

# Helper function for TEST 14
def test_early_return(flag):
    result: Imu
    if flag == 1:
        result = 10
    else:
        result = 20
    return result

# Helper function for TEST 15
def test_multi_return(flag):
    a: Imu
    b: Imu
    if flag == 1:
        a = 100
        b = 200
    else:
        assert False
    return a, b

# Helper function for TEST 22
def func_with_mut_param(x: Mut, flag):
    if flag == 1:
        x = x * 10
    else:
        assert False
    return x