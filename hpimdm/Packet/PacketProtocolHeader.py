import json
import struct
from .PacketProtocolHello import PacketProtocolHello, PacketNewProtocolHello
from .PacketProtocolSetTree import PacketProtocolUpstream, PacketNewProtocolUpstream
from .PacketProtocolRemoveTree import PacketProtocolNoLongerUpstream, PacketNewProtocolNoLongerUpstream
from .PacketProtocolInterest import PacketProtocolInterest, PacketProtocolNoInterest, PacketNewProtocolInterest,\
    PacketNewProtocolNoInterest
from .PacketProtocolAck import PacketProtocolAck, PacketNewProtocolAck
from .PacketProtocolSync import PacketProtocolHelloSync, PacketNewProtocolSync

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
        """
        Obtain Protocol Packet in a format to be transmitted (JSON)
        This method will return the Header and Payload in JSON format
        """
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
        """
        Parse received Packet from JSON and convert it into Header object... also parse Header's payload
        """
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
|Version| Type  |      Security Identifier      |Security Length|
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Security Value                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''

class PacketNewProtocolHeader(PacketPayload):
    PIM_VERSION = 0

    PIM_HDR = "! L B H B"
    PIM_HDR_LEN = struct.calcsize(PIM_HDR)

    PIM_MSG_TYPES = {PacketNewProtocolHello.PIM_TYPE: PacketNewProtocolHello,
                     PacketNewProtocolSync.PIM_TYPE: PacketNewProtocolSync,
                     PacketNewProtocolUpstream.PIM_TYPE: PacketNewProtocolUpstream,
                     PacketNewProtocolNoLongerUpstream.PIM_TYPE: PacketNewProtocolNoLongerUpstream,
                     PacketNewProtocolInterest.PIM_TYPE: PacketNewProtocolInterest,
                     PacketNewProtocolNoInterest.PIM_TYPE: PacketNewProtocolNoInterest,
                     PacketNewProtocolAck.PIM_TYPE: PacketNewProtocolAck,
                    }

    def __init__(self, payload, boot_time=0, security_id=0, security_length=0, security_value=b''):
        self.payload = payload
        self.boot_time = boot_time
        self.security_id = security_id
        self.security_length = security_length
        self.security_value = security_value

    @property
    def security_value(self):
        if self.security_length == 0:
            return b''
        else:
            len_diff = abs(len(self._security_value) - self.security_length)
            return self._security_value + b'\x00' * len_diff

    @security_value.setter
    def security_value(self, security_value):
        self._security_value = security_value

    def get_pim_type(self):
        return self.payload.PIM_TYPE

    def bytes(self) -> bytes:
        """
        Obtain Protocol Packet in a format to be transmitted (binary)
        This method will return the Header and Payload in binary format
        """
        pim_vrs_type = (PacketNewProtocolHeader.PIM_VERSION << 4) + self.get_pim_type()
        msg = struct.pack(PacketNewProtocolHeader.PIM_HDR, self.boot_time, pim_vrs_type, self.security_id,
                          self.security_length)
        msg += self.security_value + self.payload.bytes()
        return msg

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: bytes):
        """
        Parse received Packet from bits/bytes and convert them into Header object... also parse Header's payload
        """
        print("parsePimHdr: ", data)

        pim_hdr = data[0:PacketNewProtocolHeader.PIM_HDR_LEN]
        (boot_time, pim_ver_type, security_id, security_len) = struct.unpack(PacketNewProtocolHeader.PIM_HDR, pim_hdr)

        print(pim_ver_type)
        pim_version = (pim_ver_type & 0xF0) >> 4
        pim_type = pim_ver_type & 0x0F

        if pim_version != PacketNewProtocolHeader.PIM_VERSION:
            print("Version of PROTOCOL packet received not known (!=0)")
            raise Exception

        security_and_pim_payload = data[PacketNewProtocolHeader.PIM_HDR_LEN:]
        security_value = security_and_pim_payload[:security_len]
        print("Received hmac value: ", security_value)
        pim_payload = security_and_pim_payload[security_len:]
        pim_payload = PacketNewProtocolHeader.PIM_MSG_TYPES[pim_type].parse_bytes(pim_payload)
        return PacketNewProtocolHeader(pim_payload, boot_time, security_id, security_len, security_value)
