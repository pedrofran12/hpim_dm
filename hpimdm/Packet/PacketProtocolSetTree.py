import struct
import socket

###########################################################################################################
# JSON FORMAT
###########################################################################################################
class PacketProtocolUpstream():
    PIM_TYPE = "I_AM_UPSTREAM"

    def __init__(self, source, group, metric_preference, metric, sequence_number):
        self.source = source
        self.group = group
        self.metric = metric
        self.metric_preference = metric_preference
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        """
        Obtain Protocol IamUpstream Packet in a format to be transmitted (JSON)
        """
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "METRIC": self.metric,
               "METRIC_PREFERENCE": self.metric_preference,
               "SN": self.sequence_number
              }

        return msg

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Protocol IamUpstream Packet from JSON format and convert it into ProtocolUpstream object
        """
        source = data["SOURCE"]
        group = data["GROUP"]
        metric = data["METRIC"]
        metric_preference = data["METRIC_PREFERENCE"]
        sn = data["SN"]
        return cls(source, group, metric_preference, metric, sn)


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
|                       Metric Preference                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            Metric                             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketNewProtocolUpstream:
    PIM_TYPE = 2

    PIM_HDR_INSTALL = "! 4s 4s L L L"
    PIM_HDR_INSTALL_LEN = struct.calcsize(PIM_HDR_INSTALL)

    def __init__(self, source_ip, group_ip, metric_preference, metric, sequence_number):
        if type(source_ip) not in (str, bytes) or type(group_ip) not in (str, bytes):
            raise Exception
        if type(source_ip) is bytes:
            source_ip = socket.inet_ntoa(source_ip)
        if type(group_ip) is bytes:
            group_ip = socket.inet_ntoa(group_ip)

        self.source = source_ip
        self.group = group_ip
        self.metric = metric
        self.metric_preference = metric_preference
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        """
        Obtain Protocol IamUpstream Packet in a format to be transmitted (binary)
        """
        msg = struct.pack(PacketNewProtocolUpstream.PIM_HDR_INSTALL, socket.inet_aton(self.source),
                          socket.inet_aton(self.group), self.sequence_number, self.metric_preference, self.metric)

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Protocol IamUpstream Packet from binary format and convert it into ProtocolUpstream object
        """
        (tree_source, tree_group, sn, mp, m) = struct.unpack(PacketNewProtocolUpstream.PIM_HDR_INSTALL,
                                                             data[:PacketNewProtocolUpstream.PIM_HDR_INSTALL_LEN])
        return cls(tree_source, tree_group, mp, m, sn)
