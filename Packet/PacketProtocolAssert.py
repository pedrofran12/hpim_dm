import struct
import socket
from Packet.PacketPimEncodedGroupAddress import PacketPimEncodedGroupAddress
from Packet.PacketPimEncodedUnicastAddress import PacketPimEncodedUnicastAddress
from tree.globals import ASSERT_CANCEL_METRIC
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|PIM Ver| Type  |   Reserved    |           Checksum            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|         Multicast Group Address (Encoded Group Format)        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|             Source Address (Encoded Unicast Format)           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|R|                     Metric Preference                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             Metric                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolAssert:
    PIM_TYPE = "ASSERT"

    def __init__(self, multicast_group_address: str or bytes, source_address: str or bytes, metric_preference: int or float, metric: int or float):
        self.multicast_group_address = multicast_group_address
        self.source_address = source_address
        self.metric_preference = metric_preference
        self.metric = metric

    def bytes(self) -> bytes:
        msg = {"MULTICAST_GROUP": self.multicast_group_address,
               "SOURCE": self.source_address,
               "METRIC_PREFERENCE": self.metric_preference,
               "METRIC": self.metric}
        return msg

    def __len__(self):
        #not used
        return 0

    @staticmethod
    def parse_bytes(data: bytes):
        multicast_group_address = data["MULTICAST_GROUP"]
        source_address = data["SOURCE"]
        metric_preference = data["METRIC_PREFERENCE"]
        metric = data["METRIC"]

        pim_payload = PacketProtocolAssert(multicast_group_address, source_address, metric_preference, metric)
        return pim_payload
