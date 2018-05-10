import json
from Packet.PacketProtocolHello import PacketProtocolHello
from Packet.PacketProtocolSetTree import PacketProtocolInstallTree
from Packet.PacketProtocolRemoveTree import PacketProtocolUninstallTree
from Packet.PacketProtocolJoinTree import PacketProtocolInterest, PacketProtocolNoInterest
from Packet.PacketProtocolAck import PacketProtocolAck
#from Packet.PacketProtocolTreeInterestQuery import PacketProtocolQuack

from .PacketPayload import PacketPayload
'''
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Type  |   msg........                                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolHeader(PacketPayload):

    PIM_MSG_TYPES = {"HELLO": PacketProtocolHello,
                     "INTEREST": PacketProtocolInterest,
                     "NO_INTEREST": PacketProtocolNoInterest,
                     "INSTALL": PacketProtocolInstallTree,
                     "UNINSTALL": PacketProtocolUninstallTree,
                     "ACK": PacketProtocolAck,
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
