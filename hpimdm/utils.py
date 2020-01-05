import array


def checksum(pkt: bytes) -> bytes:
    """
    Calculate checksum from a buch of bytes
    """
    if len(pkt) % 2 == 1:
        pkt += "\0"
    s = sum(array.array("H", pkt))
    s = (s >> 16) + (s & 0xffff)
    s += s >> 16
    s = ~s
    return (((s >> 8) & 0xff) | s << 8) & 0xffff


import ctypes
import ctypes.util

libc = ctypes.CDLL(ctypes.util.find_library('c'))


def if_nametoindex(name):
    """
    Get index of physical interface from its name
    """
    if not isinstance(name, str):
        raise TypeError('name must be a string.')
    ret = libc.if_nametoindex(name)
    if not ret:
        raise RuntimeError("Invalid Name")
    return ret


def if_indextoname(index):
    """
    Get name of physical interface from its index
    """
    if not isinstance(index, int):
        raise TypeError('index must be an int.')
    libc.if_indextoname.argtypes = [ctypes.c_uint32, ctypes.c_char_p]
    libc.if_indextoname.restype = ctypes.c_char_p

    ifname = ctypes.create_string_buffer(32)
    ifname = libc.if_indextoname(index, ifname)
    if not ifname:
        raise RuntimeError("Invalid Index")
    return ifname.decode("utf-8")



# obtain TYPE_CHECKING (for type hinting)
try:
    from typing import TYPE_CHECKING
except ImportError:
    TYPE_CHECKING = False
