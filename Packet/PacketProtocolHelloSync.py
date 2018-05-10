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
class PacketProtocolHelloSync():
    PIM_TYPE = "INSTALL"

    def __init__(self, upstream_trees, sequence_number):
        self.sequence_number = sequence_number
        self.upstream_trees = upstream_trees

    def bytes(self) -> bytes:
        msg = {"SN": self.sequence_number,
               "TREES": self.upstream_trees,
               }

        return msg

    @classmethod
    def parse_bytes(cls, data: bytes):
        trees = data["TREES"]
        sn = data["SN"]
        return cls(trees, sn)

class PacketProtocolHelloSyncEntry():
    def __init__(self, source, group, metric_preference, metric):
        self.source = source
        self.group = group
        self.metric = metric
        self.metric_preference = metric_preference

    def __bytes__(self):
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "METRIC": self.metric,
               "METRIC_PREFERENCE": self.metric_preference,
        }

        return msg

    @staticmethod
    def parse_bytes(data: bytes):
        source = data["SOURCE"]
        group = data["GROUP"]
        metric = data["METRIC"]
        metric_preference = data["METRIC_PREFERENCE"]
        return PacketProtocolHelloSyncEntry(source, group, metric, metric_preference)
