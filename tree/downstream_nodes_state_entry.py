from Packet.PacketProtocolTreeInterestQuery import PacketProtocolQueryEntry

class StateEntry(PacketProtocolQueryEntry):
    def __init__(self, neighbor_ip, state, counter):
        super().__init__(neighbor_ip, state, counter)
