import struct
import socket

###########################################################################################################
# JSON FORMAT
###########################################################################################################
class PacketHPIMAckJson:
    PIM_TYPE = "ACK"

    def __init__(self, source, group, sequence_number, neighbor_boot_time=0, neighbor_snapshot_sn=0, my_snapshot_sn=0):
        self.source = source
        self.group = group
        self.neighbor_boot_time = neighbor_boot_time
        self.neighbor_snapshot_sn = neighbor_snapshot_sn
        self.my_snapshot_sn = my_snapshot_sn
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        """
        Obtain Packet Ack in a format to be transmitted (JSON)
        """
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "NEIGHBOR_BOOT_TIME": self.neighbor_boot_time,
               "NEIGHBOR_SNAPSHOT_SN": self.neighbor_snapshot_sn,
               "MY_SNAPSHOT_SN": self.my_snapshot_sn,
               "SN": self.sequence_number
              }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Packet from JSON and create ProtocolAck object
        """
        source = data["SOURCE"]
        group = data["GROUP"]
        sn = data["SN"]
        nbt = data["NEIGHBOR_BOOT_TIME"]
        nssn = data["NEIGHBOR_SNAPSHOT_SN"]
        mssn = data["MY_SNAPSHOT_SN"]
        return cls(source, group, sn, nbt, nssn, mssn)


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
|                       Neighbor BootTime                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       NeighborSnapshotSN                      |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          MySnapshotSN                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                     Neighbor Sequence Number                  |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketHPIMAck:
    PIM_TYPE = 6

    PIM_HDR_ACK = "! 4s 4s L L L L"
    PIM_HDR_ACK_LEN = struct.calcsize(PIM_HDR_ACK)
    FAMILY = socket.AF_INET

    def __init__(self, source_ip, group_ip, sequence_number, neighbor_boot_time=0, neighbor_snapshot_sn=0, my_snapshot_sn=0):
        if type(source_ip) not in (str, bytes) or type(group_ip) not in (str, bytes):
            raise Exception
        if type(source_ip) is bytes:
            source_ip = socket.inet_ntop(self.FAMILY, source_ip)
        if type(group_ip) is bytes:
            group_ip = socket.inet_ntop(self.FAMILY, group_ip)

        self.source = source_ip
        self.group = group_ip
        self.neighbor_boot_time = neighbor_boot_time
        self.sequence_number = sequence_number
        self.neighbor_snapshot_sn = neighbor_snapshot_sn
        self.my_snapshot_sn = my_snapshot_sn

    def bytes(self) -> bytes:
        """
        Obtain Packet Ack in a format to be transmitted (binary)
        """
        msg = struct.pack(self.PIM_HDR_ACK, socket.inet_pton(self.FAMILY, self.source),
                          socket.inet_pton(self.FAMILY, self.group), self.neighbor_boot_time, self.neighbor_snapshot_sn,
                          self.my_snapshot_sn, self.sequence_number)

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Packet from bits/bytes and convert them into ProtocolAck object
        """
        (tree_source, tree_group, neighbor_boot_time, neighbor_snapshot_sn, my_snapshot_sn, sn) =\
            struct.unpack(cls.PIM_HDR_ACK, data[:cls.PIM_HDR_ACK_LEN])
        return cls(tree_source, tree_group, sn, neighbor_boot_time, neighbor_snapshot_sn, my_snapshot_sn)


class PacketHPIMAck_v6(PacketHPIMAck):
    PIM_HDR_ACK = "! 16s 16s L L L L"
    PIM_HDR_ACK_LEN = struct.calcsize(PIM_HDR_ACK)
    FAMILY = socket.AF_INET6

    def __init__(self, source_ip, group_ip, sequence_number, neighbor_boot_time=0, neighbor_snapshot_sn=0, my_snapshot_sn=0):
        super().__init__(source_ip, group_ip, sequence_number, neighbor_boot_time, neighbor_snapshot_sn, my_snapshot_sn)
