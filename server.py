from binascii import hexlify
from ctypes import create_string_buffer, addressof
from socket import socket, AF_PACKET, SOCK_RAW, SOL_SOCKET, SOCK_DGRAM
from struct import pack, unpack

# A subset of Berkeley Packet Filter constants and macros, as defined in
# linux/filter.h.

# Instruction classes
BPF_LD = 0x00
BPF_JMP = 0x05
BPF_RET = 0x06

# ld/ldx fields
BPF_H = 0x08
BPF_B = 0x10
BPF_ABS = 0x20

# alu/jmp fields
BPF_JEQ = 0x10
BPF_K = 0x00


def bpf_jump(code, k, jt, jf):
    return pack('HBBI', code, jt, jf, k)


def bpf_stmt(code, k):
    return bpf_jump(code, k, 0, 0)


# Ordering of the filters is backwards of what would be intuitive for
# performance reasons: the check that is most likely to fail is first.
filters_list = [
    # Must have dst port 67. Load (BPF_LD) a half word value (BPF_H) in
    # ethernet frame at absolute byte offset 36 (BPF_ABS). If value is equal to
    # 67 then do not jump, else jump 5 statements.
    bpf_stmt(BPF_LD | BPF_H | BPF_ABS, 36),
    bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, 67, 0, 5),

    # Must be UDP (check protocol field at byte offset 23)
    bpf_stmt(BPF_LD | BPF_B | BPF_ABS, 23),
    bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, 0x11, 0, 3),

    # Must be IPv4 (check ethertype field at byte offset 12)
    bpf_stmt(BPF_LD | BPF_H | BPF_ABS, 12),
    bpf_jump(BPF_JMP | BPF_JEQ | BPF_K, 0x0800, 0, 1),

    bpf_stmt(BPF_RET | BPF_K, 0x0fffffff),  # pass
    bpf_stmt(BPF_RET | BPF_K, 0),  # reject
]


FILTER = [
    pack('HBBI',0x28, 0, 0, 0x0000000c),
    pack('HBBI',0x15, 7, 0, 0x000086dd),
    pack('HBBI',0x15, 0, 6, 0x00000800),
    pack('HBBI',0x30, 0, 0, 0x00000017),
    pack('HBBI',0x15, 1, 0, 0x00000011),
    pack('HBBI',0x15, 0, 3, 0x00000001),
    pack('HBBI',0x20, 0, 0, 0x0000001e),
    pack('HBBI',0x15, 0, 1, 0xe00c0c0c),
    pack('HBBI',0x6, 0, 0, 0x00040000),
    pack('HBBI',0x6, 0, 0, 0x00000000),
]



FILTER_IGMP = [
    pack('HBBI', 0x28, 0, 0, 0x0000000c),
    pack('HBBI', 0x15, 0, 3, 0x00000800),
    pack('HBBI', 0x30, 0, 0, 0x00000017),
    pack('HBBI', 0x15, 0, 1, 0x00000002),
    pack('HBBI', 0x6, 0, 0, 0x00040000),
    pack('HBBI', 0x6, 0, 0, 0x00000000),
]


# Create filters struct and fprog struct to be used by SO_ATTACH_FILTER, as
# defined in linux/filter.h.
filters = b''.join(FILTER_IGMP)
b = create_string_buffer(filters)
mem_addr_of_filters = addressof(b)
fprog = pack('HL', len(FILTER_IGMP), mem_addr_of_filters)

# As defined in asm/socket.h
SO_ATTACH_FILTER = 26

# Create listening socket with filters
s = socket(AF_PACKET, SOCK_RAW, 0x0800)
s.setsockopt(SOL_SOCKET, SO_ATTACH_FILTER, fprog)
s.bind(('wlp2s0', 0x0800))

while True:
    data, addr = s.recvfrom(5000)
    print('got data from', addr, ':', data)
