import json
import random
from Packet.PacketProtocolHello import PacketProtocolHello
from Packet.PacketProtocolAssert import PacketProtocolAssert
from Packet.PacketProtocolTreeInterestQuery import PacketProtocolTreeInterestQuery
from Packet.PacketProtocolJoin import PacketProtocolJoin


from .PacketPayload import PacketPayload
'''
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Type  |   msg........                                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolHeader(PacketPayload):

    PIM_MSG_TYPES = {"HELLO": PacketProtocolHello,
                     "ASSERT": PacketProtocolAssert,
                     "JOIN": PacketProtocolJoin,
                     "TREE_INTEREST_QUERY": PacketProtocolTreeInterestQuery,
                     "SET_TREE": None,
                     "SET_TREE_ACK": None,
                     "REMOVE_TREE": None,
                     "REMOVE_TREE_ACK": None,
                     "CONFIRM": None,
                     "CONFIRM_ACK": None
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

        id_reliable = msg["TYPE"]

        pim_payload = msg["DATA"]
        print("DATA", pim_payload)
        pim_payload = PacketProtocolHeader.PIM_MSG_TYPES[type].parse_bytes(pim_payload)
        return PacketProtocolHeader(pim_payload, id_reliable)
