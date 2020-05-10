import json
import struct
from .PacketHPIMHello import PacketHPIMHelloJson, PacketHPIMHello
from .PacketHPIMIamUpstream import PacketHPIMUpstreamJson, PacketHPIMUpstream, PacketHPIMUpstream_v6
from .PacketHPIMNotUpstream import PacketHPIMNoLongerUpstreamJson, PacketHPIMNoLongerUpstream,\
    PacketHPIMNoLongerUpstream_v6
from .PacketHPIMInterest import PacketHPIMInterestJson, PacketHPIMNoInterestJson, PacketHPIMInterest,\
    PacketHPIMNoInterest, PacketHPIMInterest_v6, PacketHPIMNoInterest_v6
from .PacketHPIMAck import PacketHPIMAckJson, PacketHPIMAck, PacketHPIMAck_v6
from .PacketHPIMSync import PacketHPIMSyncJson, PacketHPIMSync, PacketHPIMSync_v6

from .PacketPayload import PacketPayload
'''
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|  Type  |   msg........                                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketHPIMHeaderJson(PacketPayload):

    PIM_MSG_TYPES = {"HELLO": PacketHPIMHelloJson,
                     "INTEREST": PacketHPIMInterestJson,
                     "NO_INTEREST": PacketHPIMNoInterestJson,
                     "I_AM_UPSTREAM": PacketHPIMUpstreamJson,
                     "I_AM_NO_LONGER_UPSTREAM": PacketHPIMNoLongerUpstreamJson,
                     "ACK": PacketHPIMAckJson,
                     "SYNC": PacketHPIMSyncJson,
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
        pim_payload = PacketHPIMHeaderJson.PIM_MSG_TYPES[pkt_type].parse_bytes(pim_payload)
        return PacketHPIMHeaderJson(pim_payload, id_reliable)



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

class PacketHPIMHeader(PacketPayload):
    PIM_VERSION = 0

    PIM_HDR = "! L B H B"
    PIM_HDR_LEN = struct.calcsize(PIM_HDR)

    PIM_MSG_TYPES = {PacketHPIMHello.PIM_TYPE: PacketHPIMHello,
                     PacketHPIMSync.PIM_TYPE: PacketHPIMSync,
                     PacketHPIMUpstream.PIM_TYPE: PacketHPIMUpstream,
                     PacketHPIMNoLongerUpstream.PIM_TYPE: PacketHPIMNoLongerUpstream,
                     PacketHPIMInterest.PIM_TYPE: PacketHPIMInterest,
                     PacketHPIMNoInterest.PIM_TYPE: PacketHPIMNoInterest,
                     PacketHPIMAck.PIM_TYPE: PacketHPIMAck,
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
        pim_vrs_type = (PacketHPIMHeader.PIM_VERSION << 4) + self.get_pim_type()
        msg = struct.pack(PacketHPIMHeader.PIM_HDR, self.boot_time, pim_vrs_type, self.security_id,
                          self.security_length)
        msg += self.security_value + self.payload.bytes()
        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Packet from bits/bytes and convert them into Header object... also parse Header's payload
        """
        print("parsePimHdr: ", data)

        pim_hdr = data[0:cls.PIM_HDR_LEN]
        (boot_time, pim_ver_type, security_id, security_len) = struct.unpack(cls.PIM_HDR, pim_hdr)

        print(pim_ver_type)
        pim_version = (pim_ver_type & 0xF0) >> 4
        pim_type = pim_ver_type & 0x0F

        if pim_version != cls.PIM_VERSION:
            print("Version of PROTOCOL packet received not known (!=0)")
            raise Exception

        security_and_pim_payload = data[cls.PIM_HDR_LEN:]
        security_value = security_and_pim_payload[:security_len]
        print("Received hmac value: ", security_value)
        pim_payload = security_and_pim_payload[security_len:]
        pim_payload = cls.PIM_MSG_TYPES[pim_type].parse_bytes(pim_payload)
        return PacketHPIMHeader(pim_payload, boot_time, security_id, security_len, security_value)


class PacketHPIMHeader_v6(PacketHPIMHeader):
    PIM_MSG_TYPES = {PacketHPIMHello.PIM_TYPE: PacketHPIMHello,
                     PacketHPIMSync.PIM_TYPE: PacketHPIMSync_v6,
                     PacketHPIMUpstream.PIM_TYPE: PacketHPIMUpstream_v6,
                     PacketHPIMNoLongerUpstream.PIM_TYPE: PacketHPIMNoLongerUpstream_v6,
                     PacketHPIMInterest.PIM_TYPE: PacketHPIMInterest_v6,
                     PacketHPIMNoInterest.PIM_TYPE: PacketHPIMNoInterest_v6,
                     PacketHPIMAck.PIM_TYPE: PacketHPIMAck_v6,
                     }

    def __init__(self, payload, boot_time=0, security_id=0, security_length=0, security_value=b''):
        super().__init__(payload, boot_time, security_id, security_length, security_value)
