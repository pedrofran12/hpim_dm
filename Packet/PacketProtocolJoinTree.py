import struct
import socket
from Packet.PacketPimEncodedUnicastAddress import PacketPimEncodedUnicastAddress
from Packet.PacketPimJoinPruneMulticastGroup import PacketPimJoinPruneMulticastGroup
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolInterest:
    PIM_TYPE = "INTEREST"

    def __init__(self, source, group, sequence_number):
        self.source = source
        self.group = group
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "SN": self.sequence_number
               }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        source = data["SOURCE"]
        group = data["GROUP"]
        sn = data["SN"]
        return cls(source, group, sn)


class PacketProtocolNoInterest(PacketProtocolInterest):
    PIM_TYPE = "NO_INTEREST"

    def __init__(self, source, group, sn):
        super().__init__(source, group, sn)
