import struct
from abc import ABCMeta, abstractstaticmethod
from .PacketProtocolHelloOptions import PacketProtocolHelloOptions, PacketProtocolHelloNeighbors, PacketProtocolHelloHoldtime, PacketProtocolHelloGenerationID

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
class PacketProtocolHello:
    PIM_TYPE = "HELLO"

    def __init__(self):
        self.options = {}

    def add_option(self, option: 'PacketProtocolHelloOptions'):
        self.options[option.type] = option

    def get_options(self):
        return self.options

    def bytes(self) -> dict:
        res = {}
        for option in self.options.values():
            res.update(option.bytes())
        return res

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: dict):
        pim_payload = PacketProtocolHello()
        for (key, value) in data.items():
            option = PacketProtocolHelloOptions.parse_bytes((key,value))
            pim_payload.add_option(option)
        return pim_payload





###############################################################################

'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Hello HoldTime                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''


class PacketNewProtocolHello:
    PIM_TYPE = 0
    PIM_HDR_OPTS = "! L"
    PIM_HDR_OPTS_LEN = struct.calcsize(PIM_HDR_OPTS)

    def __init__(self, hello_holdtime):
        self.hello_holdtime = hello_holdtime

    def bytes(self) -> bytes:
        msg = struct.pack(PacketNewProtocolHello.PIM_HDR_OPTS, self.hello_holdtime)
        return msg

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def parse_bytes(data: bytes):
        (hello_holdtime) = struct.unpack(PacketNewProtocolHello.PIM_HDR_OPTS,
                                         data[:PacketNewProtocolHello.PIM_HDR_OPTS_LEN])
        return PacketNewProtocolHello(hello_holdtime)
