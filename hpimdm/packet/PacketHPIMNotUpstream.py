import socket
import struct
from .PacketHPIMInterest import PacketHPIMInterest, PacketHPIMInterestJson

###########################################################################################################
# JSON FORMAT
###########################################################################################################
class PacketHPIMNoLongerUpstreamJson(PacketHPIMInterestJson):
    PIM_TYPE = "I_AM_NO_LONGER_UPSTREAM"

    def __init__(self, source, group, sequence_number):
        super().__init__(source, group, sequence_number)


###########################################################################################################
# BINARY FORMAT
###########################################################################################################
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                        Tree Source IP                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Tree Group IP                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                        Sequence Number                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketHPIMNoLongerUpstream(PacketHPIMInterest):
    PIM_TYPE = 3

    def __init__(self, source_ip, group_ip, sequence_number):
        super().__init__(source_ip, group_ip, sequence_number)


class PacketHPIMNoLongerUpstream_v6(PacketHPIMNoLongerUpstream):
    PIM_HDR_INTEREST = "! 16s 16s L"
    PIM_HDR_INTEREST_LEN = struct.calcsize(PIM_HDR_INTEREST)
    FAMILY = socket.AF_INET6

    def __init__(self, source_ip, group_ip, sequence_number):
        super().__init__(source_ip, group_ip, sequence_number)
