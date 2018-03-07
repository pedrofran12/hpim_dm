from Packet.PacketProtocolJoinTree import PacketProtocolJoinTree
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolTreeInterestQuery(PacketProtocolJoinTree):
    PIM_TYPE = "TREE_INTEREST_QUERY"

    def __init__(self, source, group):
        super().__init__(source, group)

class PacketProtocolTreeInterestQueryAck(PacketProtocolTreeInterestQuery):
    PIM_TYPE = "TREE_INTEREST_QUERY_ACK"

    def __init__(self, source, group):
        super().__init__(source, group)
