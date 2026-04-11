from snark_lib import *
from ..utils import *


def main():
    build_preamble_memory()
    expected_hash = 0
    input_buf = hint_read("input")
    len = input_buf[0]
    assert len < 2**15
    debug_assert(0 < len)
    data: Mut = input_buf + 1
    hash = slice_hash_with_iv_dynamic_unroll(data, len, 15)
    copy_8(hash, expected_hash)
    return
