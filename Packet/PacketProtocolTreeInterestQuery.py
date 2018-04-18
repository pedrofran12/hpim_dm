from Packet.PacketProtocolJoinTree import PacketProtocolJoinTree
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|        Upstream Neighbor Address (Encoded Unicast Format)     |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|   Reserved    |  Num Groups   |          Hold Time            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketProtocolTreeInterestQuery(object):
    PIM_TYPE = "QUERY_ACK"

    def __init__(self, source, group, vector):
        self.source = source
        self.group = group
        self.vector = vector

    def bytes(self) -> bytes:
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "VECTOR": self.vector
               }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        source = data["SOURCE"]
        group = data["GROUP"]
        vector = data["VECTOR"]
        return PacketProtocolTreeInterestQuery(source, group, vector)


class PacketProtocolQuack(object):
    PIM_TYPE = "QUACK"

    def __init__(self, source, group, states):
        self.source = source
        self.group = group
        self.states = states

    def bytes(self) -> bytes:
        dict_state = {}
        for neighbor_ip, neighbor_state in self.states.items():
            dict_state[neighbor_ip] = neighbor_state.bytes()

        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "STATES": dict_state
               }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        source = data["SOURCE"]
        group = data["GROUP"]
        #states = data["STATES"]
        states = {}
        for neighbor_ip, neighbor_state in data["STATES"].items():
            states[neighbor_ip] = PacketProtocolQueryEntry.parse_bytes(neighbor_state)
        return cls(source, group, states)



class PacketProtocolQueryEntry(object):
    STATE_NOINFO = 0
    STATE_PRUNE = 1
    STATE_JOIN = 2
    STATE_AW = 3
    STATE_AL = 4

    def __init__(self, neighbor_ip, state, counter):
        self.neighbor_ip = neighbor_ip
        self.state = state
        self.counter = counter


    def is_better_than(self, other):
        return self.neighbor_ip == other.neighbor_ip and self.counter > other.counter

    def __eq__(self, other):
        return self.neighbor_ip == other.neighbor_ip and self.state == other.state and self.counter == other.counter


    def bytes(self) -> bytes:
        '''
        msg = {self.neighbor_ip:
                    {
                        "NEIGHBOR_IP": self.neighbor_ip,
                        "STATE": self.state,
                        "COUNTER": self.counter
                    }
               }
        '''
        msg = {"NEIGHBOR_IP": self.neighbor_ip,
               "STATE": self.state,
               "COUNTER": self.counter
               }

        return msg

    def __len__(self):
        return len(self.bytes())

    @classmethod
    def parse_bytes(cls, data: bytes):
        neighbor_ip = data["NEIGHBOR_IP"]
        state = data["STATE"]
        counter = data["COUNTER"]
        return PacketProtocolQueryEntry(neighbor_ip, state, counter)


class PacketProtocolPruneL(PacketProtocolQuack):
    PIM_TYPE = "PRUNE_L"

    def __init__(self, source, group, vector):
        super().__init__(source, group, vector)



'''
class PacketProtocolTreeInterestQueryAck(PacketProtocolTreeInterestQuery):
    PIM_TYPE = "TREE_INTEREST_QUERY_ACK"

    def __init__(self, source, group):
        super().__init__(source, group)
'''
