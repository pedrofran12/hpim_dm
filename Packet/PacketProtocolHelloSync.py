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
class PacketProtocolHelloSyncEntry():
    def __init__(self, source, group, metric_preference, metric):
        self.source = source
        self.group = group
        self.metric = metric
        self.metric_preference = metric_preference

    def bytes(self):
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
        return PacketProtocolHelloSyncEntry(source, group, metric_preference, metric)

class PacketProtocolHelloSync():
    PIM_TYPE = "HELLO_SYNC"

    def __init__(self, upstream_trees, my_sequence_number, neighbor_sequence_number):
        self.my_sequence_number = my_sequence_number
        self.neighbor_sequence_number = neighbor_sequence_number
        self.upstream_trees = upstream_trees

    def bytes(self) -> bytes:
        trees = []
        for entry in self.upstream_trees:
            trees.append(entry.bytes())

        msg = {"MY_SN": self.my_sequence_number,
               "NEIGHBOR_SN": self.neighbor_sequence_number,
               "TREES": trees,
               }

        return msg

    @classmethod
    def parse_bytes(cls, data: bytes):
        trees = []
        for entry in data["TREES"]:
            trees.append(PacketProtocolHelloSyncEntry.parse_bytes(entry))

        my_sn = data["MY_SN"]
        neighbor_sn = data["NEIGHBOR_SN"]
        return cls(trees, my_sn, neighbor_sn)

class PacketProtocolHelloSyncAck(PacketProtocolHelloSync):
    PIM_TYPE = "HELLO_SYNC_ACK"

    def __init__(self, upstream_trees, my_sequence_number, neighbor_sequence_number):
        super().__init__(upstream_trees, my_sequence_number, neighbor_sequence_number)


class PacketProtocolHelloSyncAckAck():
    PIM_TYPE = "HELLO_SYNC_ACK_ACK"

    def __init__(self, my_sequence_number, neighbor_sequence_number):
        self.my_sequence_number = my_sequence_number
        self.neighbor_sequence_number = neighbor_sequence_number

    def bytes(self) -> bytes:
        msg = {"MY_SN": self.my_sequence_number,
               "NEIGHBOR_SN": self.neighbor_sequence_number,
               }

        return msg

    @staticmethod
    def parse_bytes(data: bytes):
        my_sn = data["MY_SN"]
        neighbor_sn = data["NEIGHBOR_SN"]
        return PacketProtocolHelloSyncAckAck(my_sn, neighbor_sn)
