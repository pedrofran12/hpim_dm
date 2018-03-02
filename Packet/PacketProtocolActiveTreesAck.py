from abc import abstractmethod
from .PacketProtocolActiveTrees import PacketProtocolActiveTrees
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolActiveTreesAck(PacketProtocolActiveTrees):
    PIM_TYPE = "ACTIVE_TREES_ACK"

    def __init__(self, ack_trees):
        super().__init__()
        self.trees = ack_trees

    @abstractmethod
    def parse_bytes(data: bytes):
        return PacketProtocolActiveTreesAck(data)

