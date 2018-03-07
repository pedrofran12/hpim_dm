from abc import abstractmethod
from .PacketProtocolJoinTree import PacketProtocolJoinTree
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolConfirm(PacketProtocolJoinTree):
    PIM_TYPE = "CONFIRM"

    def __init__(self, source, group):
        super().__init__(source, group)

class PacketProtocolConfirmAck(PacketProtocolConfirm):
    PIM_TYPE = "CONFIRM_ACK"

    def __init__(self, source, group):
        super().__init__(source, group)
