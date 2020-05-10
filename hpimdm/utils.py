import array
import ctypes
import ctypes.util


def checksum(pkt: bytes) -> int:
    """
    Calculate checksum from a bunch of bytes
    """
    if len(pkt) % 2 == 1:
        pkt += "\0"
    s = sum(array.array("H", pkt))
    s = (s >> 16) + (s & 0xffff)
    s += s >> 16
    s = ~s
    return (((s >> 8) & 0xff) | s << 8) & 0xffff


LIBC = None
def _get_libc():
    """Load the libc library and cache reference to it"""
    global LIBC
    if LIBC is None:
        LIBC = ctypes.CDLL(ctypes.util.find_library('c'))
    return LIBC


def if_nametoindex(name):
    if isinstance(name, str):
        name = name.encode('utf-8')
    elif not isinstance(name, bytes):
        raise TypeError("Require unicode/bytes type for name")
    ret = _get_libc().if_nametoindex(name)
    if not ret:
        raise RuntimeError("Invalid Name")
    return ret


def if_indextoname(index):
    if not isinstance(index, int):
        raise TypeError('index must be an int.')
    _get_libc().if_indextoname.argtypes = [ctypes.c_uint32, ctypes.c_char_p]
    _get_libc().if_indextoname.restype = ctypes.c_char_p
    ifname = ctypes.create_string_buffer(32)
    ifname = _get_libc().if_indextoname(index, ifname)
    if not ifname:
        raise RuntimeError ("Inavlid Index")
    return ifname.decode("utf-8")


# obtain TYPE_CHECKING (for type hinting)
try:
    from typing import TYPE_CHECKING
except ImportError:
    TYPE_CHECKING = False
