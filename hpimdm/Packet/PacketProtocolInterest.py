import struct
import socket

###########################################################################################################
# JSON FORMAT
###########################################################################################################
class PacketProtocolInterest:
    PIM_TYPE = "INTEREST"

    def __init__(self, source, group, sequence_number):
        self.source = source
        self.group = group
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        """
        Obtain Protocol Interest Packet in a format to be transmitted (JSON)
        """
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "SN": self.sequence_number
              }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Protocol Interest Packet from JSON format and convert it into ProtocolInterest object
        """
        source = data["SOURCE"]
        group = data["GROUP"]
        sn = data["SN"]
        return cls(source, group, sn)


class PacketProtocolNoInterest(PacketProtocolInterest):
    PIM_TYPE = "NO_INTEREST"

    def __init__(self, source, group, sn):
        super().__init__(source, group, sn)

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
class PacketNewProtocolInterest:
    PIM_TYPE = 4

    PIM_HDR_INTEREST = "! 4s 4s L"
    PIM_HDR_INTEREST_LEN = struct.calcsize(PIM_HDR_INTEREST)

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
        """
        Obtain Protocol Interest Packet in a format to be transmitted (binary)
        """
        msg = struct.pack(PacketNewProtocolInterest.PIM_HDR_INTEREST, socket.inet_aton(self.source),
                          socket.inet_aton(self.group), self.sequence_number)

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Protocol Interest Packet from binary format and convert it into ProtocolInterest object
        """
        (tree_source, tree_group, sn) = struct.unpack(
            PacketNewProtocolInterest.PIM_HDR_INTEREST,
            data[:PacketNewProtocolInterest.PIM_HDR_INTEREST_LEN])
        return cls(tree_source, tree_group, sn)


class PacketNewProtocolNoInterest(PacketNewProtocolInterest):
    PIM_TYPE = 5

    def __init__(self, source_ip, group_ip, sequence_number):
        super().__init__(source_ip, group_ip, sequence_number)
