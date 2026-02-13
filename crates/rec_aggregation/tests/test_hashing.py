from snark_lib import *
from ..utils import *

def main():
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    len = pub_mem[0]
    assert len < 2**15
    debug_assert(0 < len)
    data = pub_mem + 1
    expected_hash = pub_mem + 1 + len
    hash = slice_hash_dynamic_unroll(data, len, 15)
    copy_8(hash, expected_hash)
    return
