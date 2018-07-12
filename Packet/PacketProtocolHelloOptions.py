import struct
from abc import ABCMeta, abstractmethod
import math

###################################################################################
# JSON FORMAT
###################################################################################
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
        return JSON_MSG_TYPES.get(type, PacketProtocolHelloUnknown).parse_bytes(data, type)


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


JSON_MSG_TYPES = {"HOLDTIME": PacketProtocolHelloHoldtime,
                 "CHECKPOINT_SN": PacketProtocolHelloCheckpointSN,
                 }



class PacketNewProtocolHelloOptions(metaclass=ABCMeta):
    TYPE = "UNKNOWN"
    PIM_HDR_OPTS = "! HH"
    PIM_HDR_OPTS_LEN = struct.calcsize(PIM_HDR_OPTS)
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |              Type             |             Length            |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, type: int, length: int):
        self.type = type
        self.length = length

    def bytes(self) -> bytes:
        return struct.pack(PacketNewProtocolHelloOptions.PIM_HDR_OPTS, self.type, self.length)

    def __len__(self):
        return self.PIM_HDR_OPTS_LEN + self.length

    @staticmethod
    def parse_bytes(data: bytes, type:int = None, length:int = None):
        (type, length) = struct.unpack(PacketNewProtocolHelloOptions.PIM_HDR_OPTS,
                                        data[:PacketNewProtocolHelloOptions.PIM_HDR_OPTS_LEN])
        #print("TYPE:", type)
        #print("LENGTH:", length)
        data = data[PacketNewProtocolHelloOptions.PIM_HDR_OPTS_LEN:]
        #return PIM_MSG_TYPES[type](data)
        return NEW_PROTOCOL_MSG_TYPES.get(type, PacketNewProtocolHelloUnknown).parse_bytes(data, type, length)


class PacketNewProtocolHelloHoldtime(PacketNewProtocolHelloOptions):
    TYPE = "HOLDTIME"
    PIM_HDR_OPT = "! H"
    PIM_HDR_OPT_LEN = struct.calcsize(PIM_HDR_OPT)
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |            Hold Time          |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, holdtime: int or float):
        super().__init__(type=1, length=2)
        self.holdtime = int(holdtime)

    def bytes(self) -> bytes:
        return super().bytes() + struct.pack(self.PIM_HDR_OPT, self.holdtime)

    @staticmethod
    def parse_bytes(data: bytes, type:int = None, length:int = None):
        if type is None or length is None:
            raise Exception
        (holdtime, ) = struct.unpack(PacketNewProtocolHelloHoldtime.PIM_HDR_OPT,
                                     data[:PacketNewProtocolHelloHoldtime.PIM_HDR_OPT_LEN])
        print("HOLDTIME:", holdtime)
        return PacketNewProtocolHelloHoldtime(holdtime=holdtime)


class PacketNewProtocolHelloCheckpointSN(PacketNewProtocolHelloOptions):
    TYPE = "CHECKPOINT_SN"
    PIM_HDR_OPT = "! L"
    PIM_HDR_OPT_LEN = struct.calcsize(PIM_HDR_OPT)
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                         Checkpoint SN                         |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, checkpoint_sn: int):
        super().__init__(type=2, length=4)
        self.checkpoint_sn = checkpoint_sn

    def bytes(self) -> bytes:
        return super().bytes() + struct.pack(self.PIM_HDR_OPT, self.checkpoint_sn)

    @staticmethod
    def parse_bytes(data: bytes, type:int = None, length:int = None):
        if type is None or length is None:
            raise Exception
        (checkpoint_sn, ) = struct.unpack(PacketNewProtocolHelloCheckpointSN.PIM_HDR_OPT,
                                     data[:PacketNewProtocolHelloCheckpointSN.PIM_HDR_OPT_LEN])
        print("CheckpointSN:", checkpoint_sn)
        return PacketNewProtocolHelloCheckpointSN(checkpoint_sn=checkpoint_sn)


class PacketNewProtocolHelloUnknown(PacketNewProtocolHelloOptions):
    TYPE = "UNKNOWN"
    PIM_HDR_OPT = "! L"
    PIM_HDR_OPT_LEN = struct.calcsize(PIM_HDR_OPT)
    '''
     0                   1                   2                   3
     0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    |                            Unknown                            |
    +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
    '''
    def __init__(self, type, length):
        super().__init__(type=type, length=length)
        #print("PIM Hello Option Unknown... TYPE=", type, "LENGTH=", length)

    def bytes(self) -> bytes:
        raise Exception

    @staticmethod
    def parse_bytes(data: bytes, type:int = None, length:int = None):
        if type is None or length is None:
            raise Exception
        return PacketNewProtocolHelloUnknown(type, length)


NEW_PROTOCOL_MSG_TYPES = {1: PacketNewProtocolHelloHoldtime,
                          2: PacketNewProtocolHelloCheckpointSN,
                         }
