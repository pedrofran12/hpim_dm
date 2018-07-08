import struct
from abc import ABCMeta, abstractmethod
import math

class PacketProtocolHelloOptions(metaclass=ABCMeta):
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |              Type             |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, type: str):
        self.type = type

    @abstractmethod
    def bytes(self) -> bytes:
        pass

    def __len__(self):
        # not used
        return 0

    @staticmethod
    def parse_bytes(data: tuple, type:int = None):
        type = data[0]
        data = data[1]
        return PIM_MSG_TYPES.get(type, PacketProtocolHelloUnknown).parse_bytes(data, type)


class PacketProtocolHelloHoldtime(PacketProtocolHelloOptions):
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |            Hold Time          |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''

    def __init__(self, holdtime: int or float):
        super().__init__(type="HOLDTIME")
        self.holdtime = int(holdtime)

    def bytes(self) -> dict:
        return {"HOLDTIME": self.holdtime}

    @staticmethod
    def parse_bytes(data, type:int = None):
        if type is None:
            raise Exception
        holdtime = data
        return PacketProtocolHelloHoldtime(holdtime=holdtime)



class PacketProtocolHelloCheckpointSN(PacketProtocolHelloOptions):
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Checkpoint SN                         |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, checkpoint_sn: int):
        super().__init__(type="CHECKPOINT_SN")
        self.checkpoint_sn = checkpoint_sn

    def bytes(self) -> dict:
        return {"CHECKPOINT_SN": self.checkpoint_sn}

    @staticmethod
    def parse_bytes(data, type:int = None):
        if type is None:
            raise Exception
        checkpoint_sn = data
        return PacketProtocolHelloCheckpointSN(checkpoint_sn=checkpoint_sn)


class PacketProtocolHelloNeighbors(PacketProtocolHelloOptions):

    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Neighbors....                         |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, neighbors: list):
        super().__init__(type="NEIGHBORS")
        self.neighbors = neighbors

    def bytes(self) -> dict:
        return {"NEIGHBORS": self.neighbors}

    @staticmethod
    def parse_bytes(data, type:int = None):
        if type is None:
            raise Exception
        neighbors = data
        return PacketProtocolHelloNeighbors(neighbors=neighbors)



class PacketProtocolHelloUnknown(PacketProtocolHelloOptions):
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                            Unknown                            |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, type):
        super().__init__(type=type)

    def bytes(self) -> bytes:
        raise Exception

    @staticmethod
    def parse_bytes(data, type:int = None):
        if type is None:
            raise Exception
        return PacketProtocolHelloUnknown(type)





PIM_MSG_TYPES = {"HOLDTIME": PacketProtocolHelloHoldtime,
                 "CHECKPOINT_SN": PacketProtocolHelloCheckpointSN,
                 "NEIGHBORS": PacketProtocolHelloNeighbors,
                 }
