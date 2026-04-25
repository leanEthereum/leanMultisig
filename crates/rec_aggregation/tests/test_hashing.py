from snark_lib import *
from ..utils import *


def main():
    build_preamble_memory()
    expected_hash = 0
    input_size_buf = Array(1)
    hint_witness("input_size", input_size_buf)
    len = input_size_buf[0]
    assert len < 2**15
    debug_assert(0 < len)
    data = Array(len)
    hint_witness("input", data)
    hash = slice_hash_with_iv_dynamic_unroll(data, len, 15)
    copy_8(hash, expected_hash)
    return
