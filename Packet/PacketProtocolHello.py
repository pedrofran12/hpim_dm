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
