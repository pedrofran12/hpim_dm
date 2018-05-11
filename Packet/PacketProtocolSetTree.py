from Packet.PacketProtocolJoinTree import PacketProtocolInterest
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolInstallTree():
    PIM_TYPE = "INSTALL"

    def __init__(self, source, group, metric_preference, metric, sequence_number):
        self.source = source
        self.group = group
        self.metric = metric
        self.metric_preference = metric_preference
        self.sequence_number = sequence_number

    def bytes(self) -> bytes:
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "METRIC": self.metric,
               "METRIC_PREFERENCE": self.metric_preference,
               "SN": self.sequence_number
               }

        return msg

    @classmethod
    def parse_bytes(cls, data: bytes):
        source = data["SOURCE"]
        group = data["GROUP"]
        metric = data["METRIC"]
        metric_preference = data["METRIC_PREFERENCE"]
        sn = data["SN"]
        return cls(source, group, metric_preference, metric, sn)