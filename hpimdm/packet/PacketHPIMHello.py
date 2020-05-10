import struct
from .PacketHPIMHelloOptions import PacketHPIMHelloOptionsJson, PacketHPIMHelloOptions

###########################################################################################################
# JSON FORMAT
###########################################################################################################
class PacketHPIMHelloJson:
    PIM_TYPE = "HELLO"

    def __init__(self):
        self.options = {}

    def add_option(self, option: 'PacketHPIMHelloOptionsJson'):
        self.options[option.type] = option

    def get_options(self):
        return self.options

    def bytes(self) -> dict:
        """
        Obtain Protocol Hello Packet in a format to be transmitted (JSON)
        This method will return the Hello and all its options in JSON format
        """
        res = {}
        for option in self.options.values():
            res.update(option.bytes())
        return res

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: dict):
        """
        Parse received Hello Packet from JSON format and convert it into Hello object
        """
        pim_payload = PacketHPIMHelloJson()
        for (key, value) in data.items():
            option = PacketHPIMHelloOptionsJson.parse_bytes((key, value))
            pim_payload.add_option(option)
        return pim_payload





###########################################################################################################
# BINARY FORMAT
###########################################################################################################
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          Option Type          |         Option Length         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Option Value                          |
|                              ...                              |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                               .                               |
|                               .                               |
|                               .                               |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          Option Type          |         Option Length         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Option Value                          |
|                              ...                              |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''

'''
NOT USED:
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Hello HoldTime                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          CheckpointSN                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''


class PacketHPIMHello:
    PIM_TYPE = 0
    PIM_HDR_OPTS = "! HH"
    PIM_HDR_OPTS_LEN = struct.calcsize(PIM_HDR_OPTS)


    def __init__(self):
        self.options = {}

    def add_option(self, option: 'PacketHPIMHelloOptions'):
        self.options[option.TYPE] = option

    def get_options(self):
        return self.options

    def bytes(self) -> bytes:
        """
        Obtain Protocol Hello Packet in a format to be transmitted (binary)
        This method will return the Hello and all its options in binary format
        """
        res = b''
        for option in self.options.values():
            res += option.bytes()
        return res

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: bytes):
        """
        Parse received Hello Packet from binary format and convert it into Hello object
        """
        protocol_payload = PacketHPIMHello()
        while data != b'':
            print("DATA", data)
            option = PacketHPIMHelloOptions.parse_bytes(data)
            option_length = len(option)
            data = data[option_length:]
            protocol_payload.add_option(option)
        return protocol_payload
