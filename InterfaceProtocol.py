import random
from Interface import Interface
from Packet.ReceivedPacket import ReceivedPacket
import Main
import traceback
from RWLock.RWLock import RWLockWrite
from Packet.PacketProtocolHelloOptions import *
from Packet.PacketProtocolHello import PacketProtocolHello
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
from utils import HELLO_HOLD_TIME_TIMEOUT
from threading import Timer, RLock
import ipaddress
from ReliableMsgTransmission import ReliableTransmission

from Packet.PacketProtocolActiveTrees import PacketProtocolActiveTrees, PacketProtocolActiveTreesAck
from Packet.PacketProtocolSetTree import PacketProtocolSetTree, PacketProtocolSetTreeAck
from Packet.PacketProtocolRemoveTree import PacketProtocolRemoveTree, PacketProtocolRemoveTreeAck
from Packet.PacketProtocolConfirm import PacketProtocolConfirm, PacketProtocolConfirmAck
from Packet.PacketProtocolJoinTree import PacketProtocolJoinTree, PacketProtocolJoinTreeAck
from Packet.PacketProtocolTreeInterestQuery import PacketProtocolTreeInterestQuery, PacketProtocolTreeInterestQueryAck
from Packet.PacketProtocolAssert import PacketProtocolAssertReliableAck, PacketProtocolAssert

import socket
import netifaces


class InterfaceProtocol(Interface):
    MCAST_GRP = '224.0.0.13'
    PROPAGATION_DELAY = 0.5
    OVERRIDE_INTERNAL = 2.5

    HELLO_PERIOD = 30
    TRIGGERED_HELLO_PERIOD = 5


    def __init__(self, interface_name: str, vif_index:int):
        # generation id
        self.generation_id = random.getrandbits(32)

        # Regulate transmission of Hello messages
        self.hello_timer = None

        # Synchronization period (discover active trees)
        self.synchronization_period = Timer(2 * InterfaceProtocol.HELLO_PERIOD, self.synchronization_period_ended)
        self.synchronization_period.start()
        self.trees_discovered_during_synchronization = set()

        # protocol neighbors
        self._had_neighbors = False
        self.neighbors = {}
        self.neighbors_lock = RWLockWrite()

        # reliable transmission buffer
        self.reliable_transmission_buffer = {} # Key: ID da msg ; value: ReliableMsgTransmission
        self.reliable_transmission_lock = RLock()

        # SOCKET
        ip_interface = netifaces.ifaddresses(interface_name)[netifaces.AF_INET][0]['addr']
        self.ip_interface = ip_interface

        s = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_PIM)

        # allow other sockets to bind this port too
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

        # explicitly join the multicast group on the interface specified
        #s.setsockopt(socket.SOL_IP, socket.IP_ADD_MEMBERSHIP, socket.inet_aton(Interface.MCAST_GRP) + socket.inet_aton(ip_interface))
        s.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP,
                     socket.inet_aton(Interface.MCAST_GRP) + socket.inet_aton(ip_interface))
        s.setsockopt(socket.SOL_SOCKET, 25, str(interface_name + '\0').encode('utf-8'))

        # set socket output interface
        s.setsockopt(socket.SOL_IP, socket.IP_MULTICAST_IF, socket.inet_aton(ip_interface))

        # set socket TTL to 1
        s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_TTL, 1)
        s.setsockopt(socket.IPPROTO_IP, socket.IP_TTL, 1)

        # don't receive outgoing packets
        s.setsockopt(socket.IPPROTO_IP, socket.IP_MULTICAST_LOOP, 0)

        super().__init__(interface_name, s, s, vif_index)
        super()._enable()
        self.force_send_hello()


    def get_ip(self):
        return self.ip_interface

    def _receive(self, raw_bytes):
        if raw_bytes:
            packet = ReceivedPacket(raw_bytes, self)
            self.PKT_FUNCTIONS[packet.payload.get_pim_type()](self, packet)


    def send(self, data: Packet, group_ip: str=MCAST_GRP):
        super().send(data=data.bytes(), group_ip=group_ip)

    def send_reliably(self, data: Packet, group_ip: str=MCAST_GRP):
        with self.reliable_transmission_lock:
            id_reliable = random.getrandbits(32)
            while id_reliable in self.reliable_transmission_buffer:
                id_reliable = random.getrandbits(32)

            data.payload.id_reliable = id_reliable
            if ipaddress.IPv4Address(group_ip).is_multicast:
                # all neighbors should ack
                rmsg = ReliableTransmission(self, data, message_destination=group_ip, neighbors_ips=self.neighbors.keys())
            else:
                # only one neighbor should ack (destination ip address is unicast)
                rmsg = ReliableTransmission(self, data, message_destination=group_ip, neighbors_ips={group_ip})
            self.reliable_transmission_buffer[id_reliable] = rmsg
            self.send(data=data, group_ip=group_ip)


    def synchronization_period_ended(self):
        if len(self.trees_discovered_during_synchronization) == 0:
            return

        # todo enviar confirms
        Main.kernel.flood_confirm_tree(self.trees_discovered_during_synchronization)

    #Random interval for initial Hello message on bootup or triggered Hello message to a rebooting neighbor
    def force_send_hello(self):
        if self.hello_timer is not None:
            self.hello_timer.cancel()

        hello_timer_time = random.uniform(0, self.TRIGGERED_HELLO_PERIOD)
        self.hello_timer = Timer(hello_timer_time, self.send_hello)
        self.hello_timer.start()

    def send_hello(self):
        self.hello_timer.cancel()

        pim_payload = PacketProtocolHello()
        pim_payload.add_option(PacketProtocolHelloHoldtime(holdtime=4 * self.HELLO_PERIOD))
        pim_payload.add_option(PacketProtocolHelloGenerationID(self.generation_id))

        ph = PacketProtocolHeader(pim_payload)
        packet = Packet(payload=ph)
        self.send(packet)

        # reschedule hello_timer
        self.hello_timer = Timer(self.HELLO_PERIOD, self.send_hello)
        self.hello_timer.start()

    def remove(self):
        self.hello_timer.cancel()
        self.hello_timer = None

        # send pim_hello timeout message
        pim_payload = PacketProtocolHello()
        pim_payload.add_option(PacketProtocolHelloHoldtime(holdtime=HELLO_HOLD_TIME_TIMEOUT))
        pim_payload.add_option(PacketProtocolHelloGenerationID(self.generation_id))
        ph = PacketProtocolHeader(pim_payload)
        packet = Packet(payload=ph)
        self.send(packet)

        #Main.kernel.interface_change_number_of_neighbors()
        super().remove()

    '''
    def check_number_of_neighbors(self):
        has_neighbors = len(self.neighbors) > 0
        if has_neighbors != self._had_neighbors:
            self._had_neighbors = has_neighbors
            Main.kernel.interface_change_number_of_neighbors()
    '''


    def new_or_reset_neighbor(self, neighbor_ip):
        Main.kernel.new_neighbor(self, neighbor_ip)

    '''
    def add_neighbor(self, ip, random_number, hello_hold_time):
        with self.neighbors_lock.genWlock():
            if ip not in self.neighbors:
                print("ADD NEIGHBOR")
                from Neighbor import Neighbor
                self.neighbors[ip] = Neighbor(self, ip, random_number, hello_hold_time)
                self.force_send_hello()
                self.check_number_of_neighbors()
    '''

    def get_neighbors(self):
        with self.neighbors_lock.genRlock():
            return self.neighbors.values()

    def get_neighbor(self, ip):
        with self.neighbors_lock.genRlock():
            return self.neighbors.get(ip)

    def remove_neighbor(self, ip):
        with self.neighbors_lock.genWlock():
            del self.neighbors[ip]
            other_neighbors_remain = len(self.neighbors) > 0
            Main.kernel.interface_neighbor_removal(self.vif_index, other_neighbors_remain)

    '''
    def change_interface(self):
        # check if ip change was already applied to interface
        old_ip_address = self.ip_interface
        new_ip_interface = netifaces.ifaddresses(self.interface_name)[netifaces.AF_INET][0]['addr']
        if old_ip_address == new_ip_interface:
            return
        
        self._send_socket.setsockopt(socket.SOL_IP, socket.IP_MULTICAST_IF, socket.inet_aton(new_ip_interface))

        self._recv_socket.setsockopt(socket.IPPROTO_IP, socket.IP_DROP_MEMBERSHIP,
                     socket.inet_aton(Interface.MCAST_GRP) + socket.inet_aton(old_ip_address))

        self._recv_socket.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP,
                                     socket.inet_aton(Interface.MCAST_GRP) + socket.inet_aton(new_ip_interface))

        self.ip_interface = new_ip_interface
    '''

    ###########################################
    # Recv packets
    ###########################################
    def receive_hello(self, packet):
        ip = packet.ip_header.ip_src
        print("ip = ", ip)
        options = packet.payload.payload.get_options()

        if ("HOLDTIME" in options) and ("GENERATION_ID" in options):
            hello_hold_time = options["HOLDTIME"].holdtime
            generation_id = options["GENERATION_ID"].generation_id
        else:
            raise Exception

        with self.neighbors_lock.genWlock():
            if ip not in self.neighbors:
                if hello_hold_time == 0:
                    return
                print("ADD NEIGHBOR")
                from Neighbor import Neighbor
                self.neighbors[ip] = Neighbor(self, ip, generation_id, hello_hold_time)
                self.force_send_hello()
                self.new_or_reset_neighbor(ip)
                #self.check_number_of_neighbors()
                return
            else:
                neighbor = self.neighbors[ip]

        neighbor.receive_hello(generation_id, hello_hold_time)


    def receive_assert(self, packet):
        pkt_assert = packet.payload.payload  # type: PacketProtocolAssert
        source = pkt_assert.source_address
        group = pkt_assert.multicast_group_address
        source_group = (source, group)

        try:
            Main.kernel.get_routing_entry(source_group).recv_assert_msg(self.vif_index, packet)
        except:
            traceback.print_exc()

    def receive_assert_reliable(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_assert = packet.payload.payload # type: PacketProtocolAssert
        pkt_assert_ack = PacketProtocolAssertReliableAck(pkt_assert.multicast_group_address, pkt_assert.source_address, pkt_assert.metric_preference, pkt_assert.metric)
        pkt_ack = PacketProtocolHeader(pkt_assert_ack, id_reliable=packet.payload.id_reliable)
        self.send(data=Packet(payload=pkt_ack), group_ip=ip_src)

        # process received assert
        self.receive_assert(packet)


    def receive_join_tree(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_jt = packet.payload.payload  # type: PacketProtocolJoinTree
        pkt_jt_ack = PacketProtocolJoinTreeAck(pkt_jt.source, pkt_jt.group)
        pkt_ack = PacketProtocolHeader(pkt_jt_ack, id_reliable=packet.payload.id_reliable)
        self.send(data=Packet(payload=pkt_ack), group_ip=ip_src)

        # Process JoinTree msg
        source_group = (pkt_jt.source, pkt_jt.group)
        try:
            Main.kernel.get_routing_entry(source_group).recv_join_msg(self.vif_index, packet)
        except:
            traceback.print_exc()

    def receive_tree_interest_query(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_tiq = packet.payload.payload  # type: PacketProtocolTreeInterestQuery
        pkt_tiq_ack = PacketProtocolTreeInterestQueryAck(pkt_tiq.source, pkt_tiq.group)
        pkt_ack = PacketProtocolHeader(pkt_tiq_ack, id_reliable=packet.payload.id_reliable)
        self.send(data=Packet(payload=pkt_ack), group_ip=ip_src)

        # Process TreeInterestQuery msg
        source_group = (pkt_tiq.source, pkt_tiq.group)
        try:
            Main.kernel.get_routing_entry(source_group).recv_tree_interest_query_msg(self.vif_index, packet)
        except:
            traceback.print_exc()

    def receive_confirm(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_c = packet.payload.payload  # type: PacketProtocolConfirm
        pkt_c_ack = PacketProtocolConfirmAck(pkt_c.source, pkt_c.group)
        pkt_ack = PacketProtocolHeader(pkt_c_ack, id_reliable=packet.payload.id_reliable)
        self.send(data=Packet(payload=pkt_ack), group_ip=ip_src)

        # Process Confirm msg
        Main.kernel.receive_confirm(packet)


    def receive_remove_tree(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_rt = packet.payload.payload  # type: PacketProtocolRemoveTree
        pkt_rt_ack = PacketProtocolRemoveTreeAck(pkt_rt.source, pkt_rt.group)
        pkt_ack = PacketProtocolHeader(pkt_rt_ack, id_reliable=packet.payload.id_reliable)
        self.send(data=Packet(payload=pkt_ack), group_ip=ip_src)

        # Process Remove Tree msg
        Main.kernel.receive_remove_tree(packet)


    def receive_set_tree(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_st = packet.payload.payload  # type: PacketProtocolSetTree
        pkt_st_ack = PacketProtocolSetTreeAck(pkt_st.source, pkt_st.group)
        pkt_ack = PacketProtocolHeader(pkt_st_ack, id_reliable=packet.payload.id_reliable)
        self.send(data=Packet(payload=pkt_ack), group_ip=ip_src)

        # Process Set Tree msg
        Main.kernel.receive_set_tree(packet)


    def receive_active_trees(self, packet):
        # First send ACK
        ip_src = packet.ip_header.ip_src
        pkt_at = packet.payload.payload  # type: PacketProtocolActiveTrees
        list_trees = pkt_at.trees # type: list
        active_trees_ack_pkt = PacketProtocolActiveTreesAck(list_trees)
        pkt_ack = PacketProtocolHeader(active_trees_ack_pkt, id_reliable=packet.payload.id_reliable)
        self.send(Packet(payload=pkt_ack), ip_src)

        # Process Active Trees msg
        if not self.synchronization_period.is_alive():
            res = set()
            for tree in pkt_at.trees:
                s_g = (tree["SOURCE"], tree["GROUP"])
                res.add(s_g)
            Main.kernel.flood_confirm_tree(res)
        else:
            for tree in pkt_at.trees:
                s_g = (tree["SOURCE"], tree["GROUP"])
                self.trees_discovered_during_synchronization.add(s_g)


    def receive_ack(self, packet):
        ip = packet.ip_header.ip_src
        id_reliable = packet.payload.id_reliable
        # todo testar se existe id_reliable no transmission_buffer...
        # SE USAR LOCK EXISTE POSSIBILIDADE DE DEADLOCK

        reliable_msg_at_buffer = self.reliable_transmission_buffer.get(id_reliable)
        if reliable_msg_at_buffer is not None:
            reliable_msg_at_buffer.receive_ack(ip)


    PKT_FUNCTIONS = {
        "HELLO": receive_hello,
        "JOIN_TREE": receive_join_tree,
        "JOIN_TREE_ACK": receive_ack,
        "ASSERT": receive_assert,
        "ASSERT_RELIABLE": receive_assert_reliable,
        #"ASSERT_RELIABLE_ACK": receive_assert_reliable_ack,
        "ASSERT_RELIABLE_ACK": receive_ack,
        "TREE_INTEREST_QUERY": receive_tree_interest_query,
        "TREE_INTEREST_QUERY_ACK": receive_ack,
        "ACTIVE_TREES": receive_active_trees,
        #"ACTIVE_TREES_ACK": receive_active_trees_ack,
        "ACTIVE_TREES_ACK": receive_ack,
        "SET_TREE": receive_set_tree,
        #"SET_TREE_ACK": receive_set_tree_ack,
        "SET_TREE_ACK": receive_ack,
        "REMOVE_TREE": receive_remove_tree,
        #"REMOVE_TREE_ACK": receive_remove_tree_ack,
        "REMOVE_TREE_ACK": receive_ack,
        "CONFIRM": receive_confirm,
        #"CONFIRM_ACK": receive_confirm_ack,
        "CONFIRM_ACK": receive_ack,
    }
