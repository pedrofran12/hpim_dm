from abc import abstractmethod
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolActiveTrees():
    PIM_TYPE = "ACTIVE_TREES"

    def __init__(self):
        self.trees = []

    def add_tree(self, source, group):
        tree_info = {"SOURCE": source,
                     "GROUP": group}
        if tree_info not in self.trees:
            self.trees.append(tree_info)

    def bytes(self) -> list:
        return self.trees

    def __len__(self):
        return len(self.bytes())

    @abstractmethod
    def parse_bytes(data: bytes):
        active_trees = PacketProtocolActiveTrees()
        active_trees.trees = data
        return active_trees

class PacketProtocolActiveTreesAck(PacketProtocolActiveTrees):
    PIM_TYPE = "ACTIVE_TREES_ACK"

    def __init__(self, ack_trees):
        super().__init__()
        self.trees = ack_trees

    @abstractmethod
    def parse_bytes(data: bytes):
        return PacketProtocolActiveTreesAck(data)
