import json
from Packet.PacketProtocolHello import PacketProtocolHello
from Packet.PacketProtocolAssert import PacketProtocolAssert, PacketProtocolAssertReliable, PacketProtocolAssertReliableAck
from Packet.PacketProtocolTreeInterestQuery import PacketProtocolPruneL, PacketProtocolQuack
from Packet.PacketProtocolSetTree import PacketProtocolSetTree, PacketProtocolSetTreeAck
from Packet.PacketProtocolRemoveTree import PacketProtocolRemoveTree, PacketProtocolRemoveTreeAck
from Packet.PacketProtocolConfirm import PacketProtocolConfirm, PacketProtocolConfirmAck
from Packet.PacketProtocolActiveTrees import PacketProtocolActiveTrees, PacketProtocolActiveTreesAck
from Packet.PacketProtocolJoinTree import PacketProtocolJoinTree, PacketProtocolPruneTree


from .PacketPayload import PacketPayload
'''
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Type  |   msg........                                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolHeader(PacketPayload):

    '''
    PIM_MSG_TYPES = {"HELLO": PacketProtocolHello,
                     "ASSERT": PacketProtocolAssert,
                     "ASSERT_RELIABLE": PacketProtocolAssertReliable,
                     "ASSERT_RELIABLE_ACK": PacketProtocolAssertReliableAck,
                     "JOIN_TREE": PacketProtocolJoinTree,
                     "JOIN_TREE_ACK": PacketProtocolJoinTreeAck,
                     "TREE_INTEREST_QUERY": PacketProtocolTreeInterestQuery,
                     "TREE_INTEREST_QUERY_ACK": PacketProtocolTreeInterestQueryAck,
                     "SET_TREE": PacketProtocolSetTree,
                     "SET_TREE_ACK": PacketProtocolSetTreeAck,
                     "REMOVE_TREE": PacketProtocolRemoveTree,
                     "REMOVE_TREE_ACK": PacketProtocolRemoveTreeAck,
                     "CONFIRM": PacketProtocolConfirm,
                     "CONFIRM_ACK": PacketProtocolConfirmAck,
                     "ACTIVE_TREES": PacketProtocolActiveTrees,
                     "ACTIVE_TREES_ACK": PacketProtocolActiveTreesAck
                     }
    '''
    PIM_MSG_TYPES = {"HELLO": PacketProtocolHello,
                     "ASSERT": PacketProtocolAssert,
                     "ASSERT_RELIABLE": PacketProtocolAssertReliable,
                     "ASSERT_RELIABLE_ACK": PacketProtocolAssertReliableAck,
                     "JOIN_TREE": PacketProtocolJoinTree,
                     #"JOIN_TREE_ACK": PacketProtocolJoinTreeAck,
                     "PRUNE_TREE": PacketProtocolPruneTree,
                     #"TREE_INTEREST_QUERY": PacketProtocolTreeInterestQuery,
                     #"TREE_INTEREST_QUERY_ACK": PacketProtocolTreeInterestQueryAck,
                     "PRUNE_L": PacketProtocolPruneL,
                     "QUACK": PacketProtocolQuack,

                     "SET_TREE": PacketProtocolSetTree,
                     "SET_TREE_ACK": PacketProtocolSetTreeAck,
                     "REMOVE_TREE": PacketProtocolRemoveTree,
                     "REMOVE_TREE_ACK": PacketProtocolRemoveTreeAck,
                     "CONFIRM": PacketProtocolConfirm,
                     "CONFIRM_ACK": PacketProtocolConfirmAck,
                     "ACTIVE_TREES": PacketProtocolActiveTrees,
                     "ACTIVE_TREES_ACK": PacketProtocolActiveTreesAck
                     }

    def __init__(self, payload, id_reliable = 0):
        self.payload = payload
        self.id_reliable = id_reliable

    def get_pim_type(self):
        return self.payload.PIM_TYPE

    def bytes(self) -> bytes:
        # obter mensagem e criar checksum
        pim_type = self.get_pim_type()
        data = {"TYPE": self.get_pim_type(),
                "ID_RELIABLE": self.id_reliable,
                "DATA": self.payload.bytes()}
        msg = json.dumps(data).encode()
        return msg

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: bytes):
        msg = json.loads(data.decode())

        type = msg["TYPE"]
        print("TYPE", type)

        id_reliable = msg["ID_RELIABLE"]

        pim_payload = msg["DATA"]
        print("DATA", pim_payload)
        pim_payload = PacketProtocolHeader.PIM_MSG_TYPES[type].parse_bytes(pim_payload)
        return PacketProtocolHeader(pim_payload, id_reliable)
