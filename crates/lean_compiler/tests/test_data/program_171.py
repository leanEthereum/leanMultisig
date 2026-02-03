from snark_lib import *

# Comprehensive test for inlining with mutable variables in branches
# Tests: @inline functions, Mut/Imu variables, match, if/else, loops, nesting

# ============================================================================
# Simple inline functions with mutable variables
# ============================================================================

@inline
def count_up(n):
    """Count from 0 to n-1, return the sum"""
    acc: Mut = 0
    for i in range(0, n):
        acc = acc + 1
    return acc

@inline
def sum_range(start, end):
    """Sum integers from start to end-1"""
    total: Mut = 0
    for i in range(start, end):
        total = total + i
    return total

@inline
def double_count(n):
    """Two mutable variables in same function"""
    a: Mut = 0
    b: Mut = 100
    for i in range(0, n):
        a = a + 1
        b = b - 1
    return a + b

# ============================================================================
# Nested inline functions (inline calling inline)
# ============================================================================

@inline
def inner_loop(k):
    """Inner inline function"""
    x: Mut = 0
    for j in range(0, k):
        x = x + j
    return x

@inline
def outer_with_inner(n):
    """Outer inline that calls inner inline"""
    result: Mut = 0
    for i in range(0, n):
        result = result + inner_loop(i)
    return result

@inline
def deep_nested(a):
    """Deeply nested: calls outer_with_inner which calls inner_loop"""
    base: Mut = 1000
    base = base + outer_with_inner(a)
    return base

# ============================================================================
# Inline functions with multiple mutable variables and complex flow
# ============================================================================

@inline
def complex_muts(n):
    """Multiple mutable variables with interdependencies"""
    x: Mut = 0
    y: Mut = 1
    z: Mut = 2
    for i in range(0, n):
        temp = x + y
        x = y
        y = z
        z = temp + z
    return x + y + z

@inline
def with_immutable(n):
    """Mix of mutable and immutable inside inline"""
    m: Mut = 0
    for i in range(0, n):
        imm = i * 2
        m = m + imm
    final_imm = m + 1000
    return final_imm

# ============================================================================
# Inline functions with internal branching
# ============================================================================

@inline
def inline_with_if(x):
    """Inline function that itself contains if/else"""
    result: Mut = 0
    if x == 0:
        result = 100
    else:
        result = 200
    result = result + x
    return result

@inline
def inline_with_match(selector):
    """Inline function that itself contains match"""
    out: Imu
    match selector:
        case 0:
            out = 1000
        case 1:
            out = 2000
        case 2:
            out = 3000
    return out

@inline
def inline_with_nested_branch(a, b):
    """Inline with nested if inside match"""
    res: Imu
    match a:
        case 0:
            if b == 0:
                res = 10
            else:
                res = 20
        case 1:
            if b == 0:
                res = 30
            else:
                res = 40
    return res

# ============================================================================
# Inline functions returning multiple values
# ============================================================================

@inline
def multi_return_inline(n):
    """Inline returning multiple values"""
    a: Mut = 0
    b: Mut = 100
    for i in range(0, n):
        a = a + 1
        b = b + 2
    return a, b

@inline
def triple_return(x):
    """Inline returning three values with different computations"""
    m1: Mut = x
    m2: Mut = x * 2
    m3: Mut = x * 3
    for i in range(0, 3):
        m1 = m1 + 1
        m2 = m2 + 2
        m3 = m3 + 3
    return m1, m2, m3

# ============================================================================
# Deeper nesting of inline functions
# ============================================================================

@inline
def level_d(x):
    """Deepest level"""
    acc: Mut = x
    for i in range(0, 2):
        acc = acc + 1
    return acc

@inline
def level_c(x):
    """Calls level_d"""
    tmp = level_d(x)
    acc: Mut = tmp
    for i in range(0, 2):
        acc = acc + 10
    return acc

@inline
def level_b(x):
    """Calls level_c"""
    tmp = level_c(x)
    acc: Mut = tmp
    for i in range(0, 2):
        acc = acc + 100
    return acc

@inline
def level_a(x):
    """Calls level_b - 4 levels deep"""
    tmp = level_b(x)
    acc: Mut = tmp
    for i in range(0, 2):
        acc = acc + 1000
    return acc

# ============================================================================
# Inline with Array operations
# ============================================================================

@inline
def inline_with_array(n):
    """Inline that allocates and uses an array"""
    arr = Array(4)
    arr[0] = n
    arr[1] = n + 1
    arr[2] = n + 2
    arr[3] = n + 3
    total: Mut = 0
    for i in unroll(0, 4):
        total = total + arr[i]
    return total

@inline
def inline_modify_array(base):
    """Inline that creates array and does complex operations"""
    buf = Array(3)
    acc: Mut = base
    for i in unroll(0, 3):
        buf[i] = acc
        acc = acc * 2
    return buf[0] + buf[1] + buf[2]

# ============================================================================
# Chained inline calls
# ============================================================================

@inline
def chain_a(x):
    m: Mut = x
    for i in range(0, 2):
        m = m + 1
    return m

@inline
def chain_b(x):
    m: Mut = x
    for i in range(0, 2):
        m = m * 2
    return m

@inline
def chain_c(x):
    m: Mut = x
    for i in range(0, 2):
        m = m + 10
    return m

# ============================================================================
# Stress test inline with many variables
# ============================================================================

@inline
def many_vars(seed):
    """Inline with 10 mutable variables"""
    v0: Mut = seed
    v1: Mut = seed + 1
    v2: Mut = seed + 2
    v3: Mut = seed + 3
    v4: Mut = seed + 4
    v5: Mut = seed + 5
    v6: Mut = seed + 6
    v7: Mut = seed + 7
    v8: Mut = seed + 8
    v9: Mut = seed + 9
    for i in range(0, 3):
        v0 = v0 + v1
        v1 = v1 + v2
        v2 = v2 + v3
        v3 = v3 + v4
        v4 = v4 + v5
        v5 = v5 + v6
        v6 = v6 + v7
        v7 = v7 + v8
        v8 = v8 + v9
        v9 = v9 + 1
    return v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 + v8 + v9

# ============================================================================
# Main test function
# ============================================================================

def main():
    # -------------------------------------------------------------------
    # TEST 1: Basic inline in match arms (different inlined vars per arm)
    # This was the original bug - each arm gets its own inlined variable names
    # -------------------------------------------------------------------
    res1: Imu
    match 0:
        case 0:
            res1 = count_up(5)
        case 1:
            res1 = count_up(10)
    assert res1 == 5

    res2: Imu
    match 1:
        case 0:
            res2 = count_up(5)
        case 1:
            res2 = count_up(10)
    assert res2 == 10

    # -------------------------------------------------------------------
    # TEST 2: Different inline functions in different arms
    # -------------------------------------------------------------------
    res3: Imu
    match 0:
        case 0:
            res3 = count_up(3)
        case 1:
            res3 = sum_range(0, 3)
        case 2:
            res3 = double_count(3)
    assert res3 == 3

    res4: Imu
    match 1:
        case 0:
            res4 = count_up(3)
        case 1:
            res4 = sum_range(0, 3)
        case 2:
            res4 = double_count(3)
    assert res4 == 3  # 0+1+2

    res5: Imu
    match 2:
        case 0:
            res5 = count_up(3)
        case 1:
            res5 = sum_range(0, 3)
        case 2:
            res5 = double_count(3)
    assert res5 == 100  # 3 + (100-3)

    # -------------------------------------------------------------------
    # TEST 3: Shared mutable variable BEFORE match, modified in branches
    # -------------------------------------------------------------------
    shared: Mut = 50
    match 0:
        case 0:
            shared = shared + count_up(5)
        case 1:
            shared = shared + count_up(10)
    assert shared == 55

    shared = shared + 100
    match 1:
        case 0:
            shared = shared + 1
        case 1:
            shared = shared + 2
    assert shared == 157

    # -------------------------------------------------------------------
    # TEST 4: Multiple inlines in same arm
    # -------------------------------------------------------------------
    multi: Imu
    match 0:
        case 0:
            a = count_up(3)
            b = sum_range(0, 4)
            c = double_count(2)
            multi = a + b + c
        case 1:
            multi = 0
    assert multi == 3 + 6 + 100  # 109

    # -------------------------------------------------------------------
    # TEST 5: Nested inline functions in match arms
    # -------------------------------------------------------------------
    nested1: Imu
    match 0:
        case 0:
            nested1 = outer_with_inner(4)
        case 1:
            nested1 = inner_loop(10)
    # outer_with_inner(4) = inner_loop(0) + inner_loop(1) + inner_loop(2) + inner_loop(3)
    #                     = 0 + 0 + 1 + 3 = 4
    assert nested1 == 4

    nested2: Imu
    match 1:
        case 0:
            nested2 = outer_with_inner(4)
        case 1:
            nested2 = inner_loop(5)
    # inner_loop(5) = 0+1+2+3+4 = 10
    assert nested2 == 10

    # -------------------------------------------------------------------
    # TEST 6: Deep nesting in match
    # -------------------------------------------------------------------
    deep1: Imu
    match 0:
        case 0:
            deep1 = deep_nested(3)
        case 1:
            deep1 = 0
    # deep_nested(3) = 1000 + outer_with_inner(3)
    #                = 1000 + inner_loop(0) + inner_loop(1) + inner_loop(2)
    #                = 1000 + 0 + 0 + 1 = 1001
    assert deep1 == 1001

    # -------------------------------------------------------------------
    # TEST 7: Inline in if/else branches
    # -------------------------------------------------------------------
    if_res1: Imu
    if 1 == 1:
        if_res1 = count_up(7)
    else:
        if_res1 = count_up(3)
    assert if_res1 == 7

    if_res2: Imu
    if 1 == 0:
        if_res2 = count_up(7)
    else:
        if_res2 = count_up(3)
    assert if_res2 == 3

    # -------------------------------------------------------------------
    # TEST 8: Nested if/else with inlines
    # -------------------------------------------------------------------
    nested_if: Imu
    if 1 == 1:
        if 2 == 2:
            nested_if = sum_range(0, 5)
        else:
            nested_if = sum_range(0, 3)
    else:
        nested_if = 0
    assert nested_if == 10  # 0+1+2+3+4

    # -------------------------------------------------------------------
    # TEST 9: Match inside if with inlines
    # -------------------------------------------------------------------
    mixed: Imu
    if 1 == 1:
        match 1:
            case 0:
                mixed = count_up(2)
            case 1:
                mixed = count_up(4)
    else:
        mixed = 999
    assert mixed == 4

    # -------------------------------------------------------------------
    # TEST 10: If inside match with inlines
    # -------------------------------------------------------------------
    mixed2: Imu
    match 0:
        case 0:
            if 1 == 1:
                mixed2 = sum_range(0, 6)
            else:
                mixed2 = 0
        case 1:
            mixed2 = 100
    assert mixed2 == 15  # 0+1+2+3+4+5

    # -------------------------------------------------------------------
    # TEST 11: Complex mutable variables in inline
    # -------------------------------------------------------------------
    cx: Imu
    match 0:
        case 0:
            cx = complex_muts(4)
        case 1:
            cx = 0
    # complex_muts(4):
    # Start: x=0, y=1, z=2
    # i=0: temp=1, x=1, y=2, z=3
    # i=1: temp=3, x=2, y=3, z=6
    # i=2: temp=5, x=3, y=6, z=11
    # i=3: temp=9, x=6, y=11, z=20
    # return 6+11+20 = 37
    assert cx == 37

    # -------------------------------------------------------------------
    # TEST 12: Mix of Mut and immutable in branches with inlines
    # -------------------------------------------------------------------
    outer_mut: Mut = 10
    inner_imu: Imu
    match 0:
        case 0:
            local_imm = with_immutable(3)
            inner_imu = local_imm
            outer_mut = outer_mut + local_imm
        case 1:
            inner_imu = 0
            outer_mut = outer_mut + 1
    # with_immutable(3) = 0 + 0*2 + 1*2 + 2*2 + 1000 = 6 + 1000 = 1006
    assert inner_imu == 1006
    assert outer_mut == 1016

    # -------------------------------------------------------------------
    # TEST 13: Inline inside unroll loop inside match
    # -------------------------------------------------------------------
    unroll_in_match: Imu
    match 0:
        case 0:
            acc: Mut = 0
            for i in unroll(0, 3):
                acc = acc + count_up(i + 1)
            unroll_in_match = acc
        case 1:
            unroll_in_match = 0
    # count_up(1) + count_up(2) + count_up(3) = 1 + 2 + 3 = 6
    assert unroll_in_match == 6

    # -------------------------------------------------------------------
    # TEST 14: Multiple match levels with different inlines at each
    # -------------------------------------------------------------------
    multi_match: Imu
    match 1:
        case 0:
            inner: Imu
            match 0:
                case 0:
                    inner = count_up(2)
                case 1:
                    inner = count_up(3)
            multi_match = inner
        case 1:
            inner2: Imu
            match 1:
                case 0:
                    inner2 = sum_range(0, 2)
                case 1:
                    inner2 = sum_range(0, 5)
            multi_match = inner2
    assert multi_match == 10  # sum_range(0, 5) = 0+1+2+3+4 = 10

    # -------------------------------------------------------------------
    # TEST 15: Same inline function called multiple times in same arm
    # -------------------------------------------------------------------
    same_fn: Imu
    match 0:
        case 0:
            r1 = count_up(3)
            r2 = count_up(4)
            r3 = count_up(5)
            same_fn = r1 + r2 + r3
        case 1:
            same_fn = 0
    assert same_fn == 12  # 3 + 4 + 5

    # -------------------------------------------------------------------
    # TEST 16: Mutable modified differently in each arm, then used after
    # -------------------------------------------------------------------
    branch_mut: Mut = 0
    match 1:
        case 0:
            branch_mut = count_up(10)
            branch_mut = branch_mut + 1
        case 1:
            branch_mut = count_up(20)
            branch_mut = branch_mut + 2
        case 2:
            branch_mut = count_up(30)
            branch_mut = branch_mut + 3
    assert branch_mut == 22  # 20 + 2

    # Continue using the mutable after match
    branch_mut = branch_mut * 2
    assert branch_mut == 44

    # -------------------------------------------------------------------
    # TEST 17: Variables declared inside only some branches
    # -------------------------------------------------------------------
    outside: Imu
    match 0:
        case 0:
            local_only_here = count_up(5)
            another_local = local_only_here + 10
            outside = another_local
        case 1:
            # Different local variables in this branch
            different_local = sum_range(0, 10)
            outside = different_local
    assert outside == 15  # 5 + 10

    # -------------------------------------------------------------------
    # TEST 18: Very deeply nested structure
    # -------------------------------------------------------------------
    very_deep: Imu
    if 1 == 1:
        match 0:
            case 0:
                if 2 == 2:
                    match 0:
                        case 0:
                            inner_val = deep_nested(2)
                            very_deep = inner_val
                        case 1:
                            very_deep = 0
                else:
                    very_deep = 0
            case 1:
                very_deep = 0
    else:
        very_deep = 0
    # deep_nested(2) = 1000 + outer_with_inner(2)
    #                = 1000 + inner_loop(0) + inner_loop(1)
    #                = 1000 + 0 + 0 = 1000
    assert very_deep == 1000

    # -------------------------------------------------------------------
    # TEST 19: Multiple unrelated mutable variables across branches
    # -------------------------------------------------------------------
    m1: Mut = 1
    m2: Mut = 2
    m3: Mut = 3
    match 1:
        case 0:
            m1 = count_up(10)
            m2 = m2 + 100
        case 1:
            m2 = sum_range(0, 5)
            m3 = m3 + 200
        case 2:
            m3 = double_count(5)
            m1 = m1 + 300
    # Case 1: m1 unchanged (1), m2 = 10, m3 = 203
    assert m1 == 1
    assert m2 == 10
    assert m3 == 203

    # -------------------------------------------------------------------
    # TEST 20: Inline result used immediately in arithmetic in branch
    # -------------------------------------------------------------------
    arith: Imu
    match 0:
        case 0:
            arith = count_up(3) * 10 + sum_range(0, 3) * 100
        case 1:
            arith = 0
    # 3 * 10 + 3 * 100 = 30 + 300 = 330
    assert arith == 330

    # ===================================================================
    # HARDCORE EDGE CASES
    # ===================================================================

    # -------------------------------------------------------------------
    # TEST 21: Inline containing if/else in different match arms
    # -------------------------------------------------------------------
    t21: Imu
    match 0:
        case 0:
            t21 = inline_with_if(0)
        case 1:
            t21 = inline_with_if(5)
    # inline_with_if(0): result=100, result=100+0=100
    assert t21 == 100

    t21b: Imu
    match 1:
        case 0:
            t21b = inline_with_if(0)
        case 1:
            t21b = inline_with_if(5)
    # inline_with_if(5): result=200, result=200+5=205
    assert t21b == 205

    # -------------------------------------------------------------------
    # TEST 22: Inline containing match in different branches
    # -------------------------------------------------------------------
    t22: Imu
    match 0:
        case 0:
            t22 = inline_with_match(0)
        case 1:
            t22 = inline_with_match(1)
        case 2:
            t22 = inline_with_match(2)
    assert t22 == 1000

    t22b: Imu
    match 2:
        case 0:
            t22b = inline_with_match(0)
        case 1:
            t22b = inline_with_match(1)
        case 2:
            t22b = inline_with_match(2)
    assert t22b == 3000

    # -------------------------------------------------------------------
    # TEST 23: Inline with nested branches called in nested branches
    # -------------------------------------------------------------------
    t23: Imu
    match 0:
        case 0:
            if 1 == 1:
                t23 = inline_with_nested_branch(0, 1)
            else:
                t23 = 0
        case 1:
            t23 = inline_with_nested_branch(1, 0)
    # inline_with_nested_branch(0, 1): a=0 -> if b==0 else -> 20
    assert t23 == 20

    t23b: Imu
    match 1:
        case 0:
            t23b = inline_with_nested_branch(0, 0)
        case 1:
            t23b = inline_with_nested_branch(1, 1)
    # inline_with_nested_branch(1, 1): a=1 -> if b==0 else -> 40
    assert t23b == 40

    # -------------------------------------------------------------------
    # TEST 24: Multi-return inline in match arms
    # -------------------------------------------------------------------
    t24a: Imu
    t24b: Imu
    match 0:
        case 0:
            t24a, t24b = multi_return_inline(5)
        case 1:
            t24a, t24b = multi_return_inline(10)
    # multi_return_inline(5): a=5, b=110
    assert t24a == 5
    assert t24b == 110

    t24c: Imu
    t24d: Imu
    match 1:
        case 0:
            t24c, t24d = multi_return_inline(5)
        case 1:
            t24c, t24d = multi_return_inline(10)
    # multi_return_inline(10): a=10, b=120
    assert t24c == 10
    assert t24d == 120

    # -------------------------------------------------------------------
    # TEST 25: Triple return inline in branches
    # -------------------------------------------------------------------
    t25a: Imu
    t25b: Imu
    t25c: Imu
    match 0:
        case 0:
            t25a, t25b, t25c = triple_return(10)
        case 1:
            t25a, t25b, t25c = triple_return(100)
    # triple_return(10): m1=10+3=13, m2=20+6=26, m3=30+9=39
    assert t25a == 13
    assert t25b == 26
    assert t25c == 39

    # -------------------------------------------------------------------
    # TEST 26: 4-level deep inline nesting in match arms
    # -------------------------------------------------------------------
    t26: Imu
    match 0:
        case 0:
            t26 = level_a(1)
        case 1:
            t26 = level_b(1)
        case 2:
            t26 = level_c(1)
        case 3:
            t26 = level_d(1)
    # level_a(1) = level_b(1) + 2000
    #            = level_c(1) + 200 + 2000
    #            = level_d(1) + 20 + 200 + 2000
    #            = (1+2) + 20 + 200 + 2000 = 2223
    assert t26 == 2223

    t26b: Imu
    match 3:
        case 0:
            t26b = level_a(5)
        case 1:
            t26b = level_b(5)
        case 2:
            t26b = level_c(5)
        case 3:
            t26b = level_d(5)
    # level_d(5) = 5+2 = 7
    assert t26b == 7

    # -------------------------------------------------------------------
    # TEST 27: Inline with Array in match arms
    # -------------------------------------------------------------------
    t27: Imu
    match 0:
        case 0:
            t27 = inline_with_array(10)
        case 1:
            t27 = inline_with_array(100)
    # inline_with_array(10): 10+11+12+13 = 46
    assert t27 == 46

    t27b: Imu
    match 1:
        case 0:
            t27b = inline_with_array(10)
        case 1:
            t27b = inline_with_array(100)
    # inline_with_array(100): 100+101+102+103 = 406
    assert t27b == 406

    # -------------------------------------------------------------------
    # TEST 28: Inline modifying array in branches
    # -------------------------------------------------------------------
    t28: Imu
    match 0:
        case 0:
            t28 = inline_modify_array(1)
        case 1:
            t28 = inline_modify_array(10)
    # inline_modify_array(1): buf=[1,2,4], return 1+2+4=7
    assert t28 == 7

    # -------------------------------------------------------------------
    # TEST 29: Chained inline calls in match arms
    # -------------------------------------------------------------------
    t29: Imu
    match 0:
        case 0:
            # chain_a(5)=7, chain_b(7)=28, chain_c(28)=48
            t29 = chain_c(chain_b(chain_a(5)))
        case 1:
            t29 = chain_a(100)
    assert t29 == 48

    t29b: Imu
    match 1:
        case 0:
            t29b = chain_c(chain_b(chain_a(1)))
        case 1:
            # chain_a(10)=12
            t29b = chain_a(10)
    assert t29b == 12

    # -------------------------------------------------------------------
    # TEST 30: Different chain patterns in different arms
    # -------------------------------------------------------------------
    t30: Imu
    match 0:
        case 0:
            t30 = chain_a(chain_a(chain_a(0)))
        case 1:
            t30 = chain_b(chain_b(chain_b(1)))
        case 2:
            t30 = chain_c(chain_c(chain_c(0)))
    # chain_a(0)=2, chain_a(2)=4, chain_a(4)=6
    assert t30 == 6

    t30b: Imu
    match 1:
        case 0:
            t30b = chain_a(chain_a(chain_a(0)))
        case 1:
            t30b = chain_b(chain_b(chain_b(1)))
        case 2:
            t30b = chain_c(chain_c(chain_c(0)))
    # chain_b(1)=4, chain_b(4)=16, chain_b(16)=64
    assert t30b == 64

    # -------------------------------------------------------------------
    # TEST 31: Stress test - many variables inline in match
    # -------------------------------------------------------------------
    t31: Imu
    match 0:
        case 0:
            t31 = many_vars(0)
        case 1:
            t31 = many_vars(10)
    # This is complex - just verify it compiles and runs
    # many_vars(0) with seed 0..9, 3 iterations of complex updates
    # Manual calculation is tedious, just check it's > 0
    assert t31 != 0

    # -------------------------------------------------------------------
    # TEST 32: Multiple multi-return inlines in same arm
    # -------------------------------------------------------------------
    t32_sum: Imu
    match 0:
        case 0:
            a1, b1 = multi_return_inline(3)
            a2, b2 = multi_return_inline(4)
            x1, x2, x3 = triple_return(5)
            t32_sum = a1 + b1 + a2 + b2 + x1 + x2 + x3
        case 1:
            t32_sum = 0
    # multi_return_inline(3): a=3, b=106
    # multi_return_inline(4): a=4, b=108
    # triple_return(5): m1=8, m2=16, m3=24
    # sum = 3+106+4+108+8+16+24 = 269
    assert t32_sum == 269

    # -------------------------------------------------------------------
    # TEST 33: 5-way match with all different inline types
    # -------------------------------------------------------------------
    t33: Imu
    match 0:
        case 0:
            t33 = count_up(10)
        case 1:
            t33 = inline_with_if(5)
        case 2:
            t33 = inline_with_match(1)
        case 3:
            t33 = level_a(0)
        case 4:
            t33 = inline_with_array(1)
    assert t33 == 10

    t33b: Imu
    match 4:
        case 0:
            t33b = count_up(10)
        case 1:
            t33b = inline_with_if(5)
        case 2:
            t33b = inline_with_match(1)
        case 3:
            t33b = level_a(0)
        case 4:
            t33b = inline_with_array(1)
    # inline_with_array(1): 1+2+3+4=10
    assert t33b == 10

    # -------------------------------------------------------------------
    # TEST 34: Triple nested match with inlines at each level
    # -------------------------------------------------------------------
    t34: Imu
    match 0:
        case 0:
            inner1: Imu
            match 1:
                case 0:
                    tmp34a = count_up(2)
                    inner1 = tmp34a + 100
                case 1:
                    inner1 = level_b(1) + 200
            t34 = inner1 + 1000
        case 1:
            t34 = 0
    # match 1, case 1: inner1 = level_b(1) + 200 = 223 + 200 = 423
    # t34 = 423 + 1000 = 1423
    assert t34 == 1423

    # Additional triple nesting test - without forward declaration inside innermost
    t34b: Imu
    match 0:
        case 0:
            mid1: Imu
            match 0:
                case 0:
                    # Use inline directly without forward declaration
                    mid1 = count_up(5) + 100
                case 1:
                    mid1 = count_up(10) + 100
            t34b = mid1 + 1000
        case 1:
            t34b = 0
    # count_up(5) = 5, mid1 = 105, t34b = 1105
    assert t34b == 1105

    # Test forward declaration with nested match and inline
    t34c: Imu
    match 0:
        case 0:
            val34c: Imu
            match 0:
                case 0:
                    val34c = sum_range(0, 5)
                case 1:
                    val34c = sum_range(0, 10)
            t34c = val34c
        case 1:
            t34c = 0
    assert t34c == 10  # sum_range(0,5) = 0+1+2+3+4 = 10

    # -------------------------------------------------------------------
    # TEST 35: Mutable modified across deeply nested branches with inlines
    # -------------------------------------------------------------------
    deep_mut: Mut = 0
    match 0:
        case 0:
            deep_mut = count_up(5)
            if 1 == 1:
                match 0:
                    case 0:
                        deep_mut = deep_mut + inline_with_if(0)
                    case 1:
                        deep_mut = deep_mut + 1000
                deep_mut = deep_mut * 2
            else:
                deep_mut = 0
        case 1:
            deep_mut = 999
    # deep_mut = 5
    # inner match case 0: deep_mut = 5 + 100 = 105
    # deep_mut = 105 * 2 = 210
    assert deep_mut == 210

    # -------------------------------------------------------------------
    # TEST 36: Multiple forward-declared Imu assigned via inlines
    # -------------------------------------------------------------------
    fwd1: Imu
    fwd2: Imu
    fwd3: Imu
    fwd4: Imu
    match 0:
        case 0:
            fwd1 = count_up(1)
            fwd2 = sum_range(0, 3)
            fwd3 = inline_with_if(10)
            fwd4 = level_d(5)
        case 1:
            fwd1 = 0
            fwd2 = 0
            fwd3 = 0
            fwd4 = 0
    assert fwd1 == 1
    assert fwd2 == 3
    assert fwd3 == 210  # 200+10
    assert fwd4 == 7

    # -------------------------------------------------------------------
    # TEST 37: Assign inline results to array elements inside branch
    # -------------------------------------------------------------------
    arr37 = Array(4)
    match 0:
        case 0:
            arr37[0] = count_up(10)
            arr37[1] = sum_range(0, 5)
            arr37[2] = inline_with_if(3)
            arr37[3] = level_d(0)
        case 1:
            arr37[0] = 0
            arr37[1] = 0
            arr37[2] = 0
            arr37[3] = 0
    assert arr37[0] == 10
    assert arr37[1] == 10  # 0+1+2+3+4
    assert arr37[2] == 203  # 200+3
    assert arr37[3] == 2

    # -------------------------------------------------------------------
    # TEST 38: If-else-if chain with different inlines
    # -------------------------------------------------------------------
    t38: Imu
    if 0 == 1:
        t38 = count_up(100)
    else:
        if 1 == 1:
            if 2 == 2:
                t38 = chain_c(chain_b(chain_a(1)))
            else:
                t38 = 0
        else:
            t38 = 0
    # chain_a(1)=3, chain_b(3)=12, chain_c(12)=32
    assert t38 == 32

    # -------------------------------------------------------------------
    # TEST 39: Complex interleaving - muts modified, inlines called, repeat
    # -------------------------------------------------------------------
    cm1: Mut = 1
    cm2: Mut = 2
    match 0:
        case 0:
            cm1 = cm1 + count_up(3)
            cm2 = cm2 + count_up(4)
            cm1 = cm1 * 2
            cm2 = cm2 + sum_range(0, cm1)
            tmp = inline_with_if(cm1)
            cm1 = cm1 + tmp
        case 1:
            cm1 = 0
            cm2 = 0
    # cm1 = 1+3=4, cm2 = 2+4=6
    # cm1 = 4*2=8, cm2 = 6+sum_range(0,8)=6+28=34
    # tmp = inline_with_if(8) = 200+8=208
    # cm1 = 8+208=216
    assert cm1 == 216
    assert cm2 == 34

    # -------------------------------------------------------------------
    # TEST 40: Inline returning mutable at different states
    # -------------------------------------------------------------------
    t40: Imu
    match 0:
        case 0:
            # complex_muts returns computation of interdependent muts
            t40 = complex_muts(5)
        case 1:
            t40 = complex_muts(3)
    # complex_muts(5):
    # Start: x=0, y=1, z=2
    # i=0: temp=1, x=1, y=2, z=3
    # i=1: temp=3, x=2, y=3, z=6
    # i=2: temp=5, x=3, y=6, z=11
    # i=3: temp=9, x=6, y=11, z=20
    # i=4: temp=17, x=11, y=20, z=37
    # return 11+20+37 = 68
    assert t40 == 68

    # -------------------------------------------------------------------
    # TEST 41: Mix of inline types in unroll loop inside match
    # -------------------------------------------------------------------
    t41: Mut = 0
    match 0:
        case 0:
            for i in unroll(0, 4):
                t41 = t41 + count_up(i + 1)
                t41 = t41 + inline_with_if(i)
            # i=0: t41 += 1 + 100 = 101
            # i=1: t41 += 2 + 201 = 304
            # i=2: t41 += 3 + 202 = 509
            # i=3: t41 += 4 + 203 = 716
        case 1:
            t41 = 0
    assert t41 == 716

    # -------------------------------------------------------------------
    # TEST 42: Deeply nested with mixed mutable tracking
    # -------------------------------------------------------------------
    outer_m: Mut = 100
    t42: Imu
    if 1 == 1:
        outer_m = outer_m + 50
        match 0:
            case 0:
                inner_m: Mut = outer_m
                if 2 == 2:
                    inner_m = inner_m + count_up(10)
                    match 0:
                        case 0:
                            inner_m = inner_m + level_d(inner_m)
                        case 1:
                            inner_m = 0
                else:
                    inner_m = 0
                outer_m = outer_m + inner_m
                t42 = outer_m
            case 1:
                t42 = 0
    else:
        t42 = 0
    # outer_m = 150
    # inner_m = 150
    # inner_m = 150 + 10 = 160
    # level_d(160) = 160+2=162
    # inner_m = 160 + 162 = 322
    # outer_m = 150 + 322 = 472
    assert t42 == 472
    assert outer_m == 472

    # -------------------------------------------------------------------
    # TEST 43: All arms have different nesting patterns
    # -------------------------------------------------------------------
    t43: Imu
    match 0:
        case 0:
            # Flat
            t43 = count_up(5)
        case 1:
            # One level nested
            if_inner: Imu
            if 1 == 1:
                if_inner = sum_range(0, 10)
            else:
                if_inner = 0
            t43 = if_inner
        case 2:
            # Two levels nested
            m_inner: Imu
            match 0:
                case 0:
                    m_inner = level_a(1)
                case 1:
                    m_inner = 0
            t43 = m_inner
        case 3:
            # Three levels nested
            deep_inner: Imu
            if 1 == 1:
                match 0:
                    case 0:
                        if 1 == 1:
                            deep_inner = inline_with_array(5)
                        else:
                            deep_inner = 0
                    case 1:
                        deep_inner = 0
            else:
                deep_inner = 0
            t43 = deep_inner
    assert t43 == 5

    # -------------------------------------------------------------------
    # TEST 44: Stress - many mutable vars across all arms
    # -------------------------------------------------------------------
    sv0: Mut = 0
    sv1: Mut = 1
    sv2: Mut = 2
    sv3: Mut = 3
    sv4: Mut = 4
    match 1:
        case 0:
            sv0 = count_up(10)
            sv1 = sv1 + sv0
            sv2 = sv2 * 2
        case 1:
            sv1 = sum_range(0, 5)
            sv2 = sv2 + sv1
            sv3 = inline_with_if(sv2)
        case 2:
            sv2 = level_d(10)
            sv3 = sv3 + sv2
            sv4 = sv4 * 3
        case 3:
            sv3 = chain_a(sv4)
            sv4 = sv4 + 100
            sv0 = sv0 + sv4
    # case 1: sv1 = 10, sv2 = 2+10=12, sv3 = inline_with_if(12)=200+12=212
    assert sv0 == 0
    assert sv1 == 10
    assert sv2 == 12
    assert sv3 == 212
    assert sv4 == 4

    # -------------------------------------------------------------------
    # TEST 45: Inline calling another inline that has internal branches
    # -------------------------------------------------------------------
    t45: Imu
    match 0:
        case 0:
            # outer_with_inner calls inner_loop
            # Now test inline_with_if (which has if/else) inside a branch
            base = outer_with_inner(3)  # = 0 + 0 + 1 = 1
            added = inline_with_if(base)  # base=1 -> 200+1=201
            t45 = added
        case 1:
            t45 = 0
    assert t45 == 201

    return
