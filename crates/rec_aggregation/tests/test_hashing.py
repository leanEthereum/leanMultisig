from snark_lib import *
from ..utils import *


def main():
    build_preamble_memory()
    expected_hash = 0
    after_preamble: Mut = PREAMBLE_MEMORY_END
    len = after_preamble[0]
    assert len < 2**15
    debug_assert(0 < len)
    data: Mut = PREAMBLE_MEMORY_END + 1
    hash = slice_hash_with_iv_dynamic_unroll(data, len, 15)
    copy_8(hash, expected_hash)
    return
