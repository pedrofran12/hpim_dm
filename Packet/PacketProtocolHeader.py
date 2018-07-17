import json
import struct
from utils import checksum
from Packet.PacketProtocolHello import PacketProtocolHello, PacketNewProtocolHello
from Packet.PacketProtocolSetTree import PacketProtocolUpstream, PacketNewProtocolUpstream
from Packet.PacketProtocolRemoveTree import PacketProtocolNoLongerUpstream, PacketNewProtocolNoLongerUpstream
from Packet.PacketProtocolInterest import PacketProtocolInterest, PacketProtocolNoInterest, PacketNewProtocolInterest,\
    PacketNewProtocolNoInterest
from Packet.PacketProtocolAck import PacketProtocolAck, PacketNewProtocolAck
from Packet.PacketProtocolSync import PacketProtocolHelloSync, PacketNewProtocolSync

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
                     "I_AM_UPSTREAM": PacketProtocolUpstream,
                     "I_AM_NO_LONGER_UPSTREAM": PacketProtocolNoLongerUpstream,
                     "ACK": PacketProtocolAck,

                     "SYNC": PacketProtocolHelloSync,
                    }

    def __init__(self, payload, boot_time=0):
        self.payload = payload
        self.boot_time = boot_time

    def get_pim_type(self):
        return self.payload.PIM_TYPE

    def bytes(self) -> bytes:
        # obter mensagem e criar checksum
        data = {"TYPE": self.get_pim_type(),
                "BOOT_TIME": self.boot_time,
                "DATA": self.payload.bytes()}
        msg = json.dumps(data).encode()
        return msg

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: bytes):
        msg = json.loads(data.decode())

        pkt_type = msg["TYPE"]
        print("TYPE", pkt_type)

        id_reliable = msg["BOOT_TIME"]

        pim_payload = msg["DATA"]
        print("DATA", pim_payload)
        pim_payload = PacketProtocolHeader.PIM_MSG_TYPES[pkt_type].parse_bytes(pim_payload)
        return PacketProtocolHeader(pim_payload, id_reliable)



'''
HEADER IN BYTE FORMAT
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            BootTime                           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|Version| Type  |  (MAYBE SECURITY)                             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''

class PacketNewProtocolHeader(PacketPayload):
    PIM_VERSION = 0

    PIM_HDR = "! L BB H"
    PIM_HDR_LEN = struct.calcsize(PIM_HDR)

    PIM_MSG_TYPES = {PacketNewProtocolHello.PIM_TYPE: PacketNewProtocolHello,
                     PacketNewProtocolSync.PIM_TYPE: PacketNewProtocolSync,
                     PacketNewProtocolUpstream.PIM_TYPE: PacketNewProtocolUpstream,
                     PacketNewProtocolNoLongerUpstream.PIM_TYPE: PacketNewProtocolNoLongerUpstream,
                     PacketNewProtocolInterest.PIM_TYPE: PacketNewProtocolInterest,
                     PacketNewProtocolNoInterest.PIM_TYPE: PacketNewProtocolNoInterest,
                     PacketNewProtocolAck.PIM_TYPE: PacketNewProtocolAck,
                    }

    def __init__(self, payload, boot_time=0):
        self.payload = payload
        self.boot_time = boot_time


    def get_pim_type(self):
        return self.payload.PIM_TYPE

    def bytes(self) -> bytes:
        # obter mensagem e criar checksum
        pim_vrs_type = (PacketNewProtocolHeader.PIM_VERSION << 4) + self.get_pim_type()
        msg = struct.pack(PacketNewProtocolHeader.PIM_HDR, self.boot_time, pim_vrs_type, 0, 0)
        msg += self.payload.bytes()
        #pim_checksum = checksum(msg_without_chcksum)
        #msg = msg_without_chcksum[0:2] + msg_without_chcksum[4:]
        return msg

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: bytes):
        print("parsePimHdr: ", data)

        pim_hdr = data[0:PacketNewProtocolHeader.PIM_HDR_LEN]
        (boot_time, pim_ver_type, _, _) = struct.unpack(PacketNewProtocolHeader.PIM_HDR, pim_hdr)

        print(pim_ver_type)
        pim_version = (pim_ver_type & 0xF0) >> 4
        pim_type = pim_ver_type & 0x0F

        if pim_version != PacketNewProtocolHeader.PIM_VERSION:
            print("Version of PROTOCOL packet received not known (!=0)")
            raise Exception

        #msg_to_checksum = data[0:2] + b'\x00\x00' + data[4:]
        #if checksum(msg_to_checksum) != rcv_checksum:
        #    print("wrong checksum")
        #    print("checksum calculated: " + str(checksum(msg_to_checksum)))
        #    print("checksum recv: " + str(rcv_checksum))
        #    raise Exception

        pim_payload = data[PacketNewProtocolHeader.PIM_HDR_LEN:]
        pim_payload = PacketNewProtocolHeader.PIM_MSG_TYPES[pim_type].parse_bytes(pim_payload)
        return PacketNewProtocolHeader(pim_payload, boot_time)
