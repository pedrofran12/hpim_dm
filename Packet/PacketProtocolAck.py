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
class PacketProtocolAck:
    PIM_TYPE = "ACK"

    def __init__(self, source, group, sequence_number, neighbor_boot_time=0):
        self.source = source
        self.group = group
        self.neighbor_boot_time = neighbor_boot_time
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "NEIGHBOR_BOOT_TIME": self.neighbor_boot_time,
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
        nbt = data["NEIGHBOR_BOOT_TIME"]
        return cls(source, group, sn, nbt)

#######################################################################################
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
class PacketNewProtocolAck:
    PIM_TYPE = 7

    PIM_HDR_ACK = "! L L L"
    PIM_HDR_ACK_LEN = struct.calcsize(PIM_HDR_ACK)

    def __init__(self, source_ip, group_ip, sequence_number):
        if type(source_ip) not in (str, bytes) or type(group_ip) not in (str, bytes):
            raise Exception
        if type(source_ip) is bytes:
            source_ip = socket.inet_ntoa(source_ip)
        if type(group_ip) is bytes:
            group_ip = socket.inet_ntoa(group_ip)

        self.source = source_ip
        self.group = group_ip
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        msg = struct.pack(PacketNewProtocolAck.PIM_HDR_ACK, socket.inet_aton(self.source),
                          socket.inet_aton(self.group), self.sequence_number)

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        (tree_source, tree_group, sn) = struct.unpack(PacketNewProtocolAck.PIM_HDR_ACK,
                                                   data[:PacketNewProtocolAck.PIM_HDR_ACK_LEN])
        return cls(tree_source, tree_group, sn)
