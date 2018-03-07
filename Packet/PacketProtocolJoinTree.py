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
class PacketProtocolJoinTree:
    PIM_TYPE = "JOIN_TREE"

    def __init__(self, source, group):
        self.source = source
        self.group = group

    def bytes(self) -> bytes:
        msg = {"SOURCE": self.source,
               "GROUP": self.group
               }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        source = data["SOURCE"]
        group = data["GROUP"]
        return cls(source, group)


class PacketProtocolJoinTreeAck(PacketProtocolJoinTree):
    PIM_TYPE = "JOIN_TREE_ACK"

    def __init__(self, source, group):
        super().__init__(source, group)
