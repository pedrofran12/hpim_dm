import random
from Interface import Interface
from Neighbor import Neighbor
import Main
import traceback
from tree.globals import MSG_FORMAT
if MSG_FORMAT == "BINARY":
    from Packet.PacketProtocolHelloOptions import PacketNewProtocolHelloHoldtime as PacketProtocolHelloHoldtime, \
        PacketNewProtocolHelloCheckpointSN as PacketProtocolHelloCheckpointSN
    from Packet.PacketProtocolHello import PacketNewProtocolHello as PacketProtocolHello
    from Packet.PacketProtocolHeader import PacketNewProtocolHeader as PacketProtocolHeader
    from Packet.PacketProtocolSync import PacketNewProtocolSyncEntry as PacketProtocolHelloSyncEntry,\
        PacketNewProtocolSync as PacketProtocolHelloSync
    from Packet.PacketProtocolInterest import PacketNewProtocolNoInterest as PacketProtocolNoInterest,\
        PacketNewProtocolInterest as PacketProtocolInterest
    from Packet.PacketProtocolSetTree import PacketNewProtocolUpstream as PacketProtocolUpstream
    from Packet.PacketProtocolRemoveTree import PacketNewProtocolNoLongerUpstream as PacketProtocolNoLongerUpstream
    from Packet.PacketProtocolAck import PacketNewProtocolAck as PacketProtocolAck
else:
    from Packet.PacketProtocolHelloOptions import PacketProtocolHelloHoldtime, PacketProtocolHelloCheckpointSN
    from Packet.PacketProtocolHello import PacketProtocolHello
    from Packet.PacketProtocolHeader import PacketProtocolHeader
    from Packet.PacketProtocolSync import PacketProtocolHelloSync
    from Packet.PacketProtocolSetTree import PacketProtocolUpstream
    from Packet.PacketProtocolInterest import PacketProtocolNoInterest, PacketProtocolInterest
    from Packet.PacketProtocolSync import PacketProtocolHelloSyncEntry
    from Packet.PacketProtocolRemoveTree import PacketProtocolNoLongerUpstream
    from Packet.PacketProtocolAck import PacketProtocolAck

from Packet.ReceivedPacket import ReceivedPacket
from Packet.Packet import Packet
from utils import HELLO_HOLD_TIME_TIMEOUT
from threading import Timer, RLock

from ReliableMsgTransmission import ReliableMessageTransmission

import socket
import netifaces
import time


class InterfaceProtocol(Interface):
    MCAST_GRP = '224.0.0.13'

    MAX_SEQUENCE_NUMBER = (2**32-1)#45 <- test with lower MAXIMUM_SEQUENCE_NUMBER

    HELLO_PERIOD = 30
    TRIGGERED_HELLO_PERIOD = 5


    def __init__(self, interface_name: str, vif_index:int):
        # Generate BootTime
        self.time_of_boot = int(time.time())

        # Regulate transmission of Hello messages
        self.hello_timer = None

        # protocol neighbors
        self._had_neighbors = False
        self.neighbors = {}
        self.neighbors_lock = RLock()

        # reliable transmission buffer
        self.reliable_transmission_buffer = {} # Key: ID da msg ; value: ReliableMsgTransmission
        self.reliable_transmission_lock = RLock()

        # sequencer for msg reliability
        self.sequencer = 0
        self.sequencer_lock = RLock()

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
        #super()._enable()
        self.force_send_hello()


    def get_ip(self):
        return self.ip_interface

    def _receive(self, raw_bytes):
        if raw_bytes:
            packet = ReceivedPacket(raw_bytes, self)
            self.PKT_FUNCTIONS[packet.payload.get_pim_type()](self, packet)

    def send(self, data: Packet, group_ip: str=MCAST_GRP):
        super().send(data=data.bytes(), group_ip=group_ip)

    def get_sequence_number(self):
        with self.sequencer_lock:
            self.sequencer += 1

            if self.sequencer == InterfaceProtocol.MAX_SEQUENCE_NUMBER:
                self.time_of_boot = int(time.time())
                self.sequencer = 1
                self.clear_reliable_transmission()
                self.force_send_hello()

            return (self.time_of_boot, self.sequencer)

    def get_checkpoint_sn(self):
        ongoing_sync_or_ongoing_reliable_transmission = False
        checkpoint_sn = 0
        # TODO VERIFICAR LOCK
        print("A ENTRAR CHECK_SN")
        with self.neighbors_lock:
            with self.sequencer_lock:
                with self.reliable_transmission_lock:
                    time_of_boot = self.time_of_boot
                    for n in list(self.neighbors.values()):
                        (neighbor_boot_time, neighbor_checkpoint_sn) = n.get_checkpoint_sn()
                        if not ongoing_sync_or_ongoing_reliable_transmission and neighbor_boot_time == time_of_boot or \
                                ongoing_sync_or_ongoing_reliable_transmission and neighbor_boot_time == time_of_boot and checkpoint_sn > neighbor_checkpoint_sn:
                            ongoing_sync_or_ongoing_reliable_transmission = True
                            checkpoint_sn = neighbor_checkpoint_sn

                    for rt in self.reliable_transmission_buffer.values():
                        (msg_boot_time, msg_checkpoint_sn) = rt.get_sequence_number()
                        if not ongoing_sync_or_ongoing_reliable_transmission and msg_boot_time==time_of_boot or \
                                ongoing_sync_or_ongoing_reliable_transmission and msg_boot_time==time_of_boot and checkpoint_sn > msg_checkpoint_sn:
                            ongoing_sync_or_ongoing_reliable_transmission = True
                            checkpoint_sn = msg_checkpoint_sn

                    if not ongoing_sync_or_ongoing_reliable_transmission:
                        checkpoint_sn = self.sequencer

                    print("A SAIR CHECK_SN")
                    return (time_of_boot, checkpoint_sn)

    #########################
    # Check neighbor status
    #######################


    #########################

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

        with self.neighbors_lock:
            with self.sequencer_lock:
                with self.reliable_transmission_lock:
                    (bt, checkpoint_sn) = self.get_checkpoint_sn()
                    if bt == self.time_of_boot:
                        pim_payload.add_option(PacketProtocolHelloCheckpointSN(checkpoint_sn))

                ph = PacketProtocolHeader(pim_payload, boot_time=self.time_of_boot)
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
        #pim_payload.add_option(PacketProtocolHelloGenerationID(self.generation_id))
        ph = PacketProtocolHeader(pim_payload, boot_time=self.time_of_boot)
        packet = Packet(payload=ph)
        self.send(packet)

        #Main.kernel.interface_change_number_of_neighbors()
        super().remove()
        self.clear_reliable_transmission()

    def snapshot_multicast_routing_table(self):
        with Main.kernel.rwlock.genWlock():
            with self.sequencer_lock:
                (snapshot_bt, snapshot_sn) = self.get_sequence_number()

                trees_to_sync = Main.kernel.snapshot_multicast_routing_table(self)  # type: dict
                #tree_to_sync_in_msg_format = []
                tree_to_sync_in_msg_format = {}

                for (source_group, state) in trees_to_sync.items():
                    #tree_to_sync_in_msg_format.append(PacketProtocolHelloSyncEntry(source_group[0], source_group[1], state.metric_preference, state.route_metric))
                    tree_to_sync_in_msg_format[source_group] = PacketProtocolHelloSyncEntry(source_group[0], source_group[1], state.metric_preference, state.route_metric)

                return (snapshot_bt, snapshot_sn, tree_to_sync_in_msg_format)

    def get_tree_state(self, source_group):
        interest_state = False
        upstream_state = None
        for n in list(self.neighbors.values()):
            (neighbor_interest_state, neighbor_upstream_state) = n.get_tree_state(tree=source_group)
            if not interest_state and neighbor_interest_state:
                interest_state = neighbor_interest_state

            if neighbor_upstream_state is not None:
                if upstream_state is None:
                    upstream_state = neighbor_upstream_state
                elif neighbor_upstream_state.is_better_than(upstream_state):
                    upstream_state = neighbor_upstream_state

        print("GET_TREE_STATE_INTERFACE INTEREST:", interest_state)
        print("GET_TREE_STATE_INTERFACE UPSTREAM:", upstream_state)
        return (interest_state, upstream_state)

    def remove_tree_state(self, source_ip, group_ip):
        for n in list(self.neighbors.values()):
            n.remove_tree_state(source_ip, group_ip)

    # Used to show list of neighbors in CLI interfaces
    def get_neighbors(self):
        with self.neighbors_lock:
            return self.neighbors.values()


    def did_all_neighbors_acked(self, neighbors_that_acked:set):
        #with self.neighbors_lock:
        return neighbors_that_acked >= self.neighbors.keys()

    def is_neighbor(self, neighbor_ip):
        return neighbor_ip in self.neighbors

    '''
    def get_neighbor(self, ip):
        with self.neighbors_lock.genRlock():
            return self.neighbors.get(ip)
    '''

    def remove_neighbor(self, ip):
        with self.neighbors_lock:
            if ip not in self.neighbors:
                return
            self.neighbors.pop(ip)
            #del self.neighbors[ip]

            # verifiar todas as arvores
            print("REMOVER ANTES RECHECK")
            Main.kernel.recheck_all_trees(self)
            print("REMOVER DEPOIS RECHECK")
            #other_neighbors_remain = len(self.neighbors) > 0
            #Main.kernel.interface_neighbor_removal(self.vif_index, other_neighbors_remain)

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
    def new_neighbor(self, neighbor_ip, boot_time, detected_via_non_sync_msg=True):
        with self.neighbors_lock:
            self.neighbors[neighbor_ip] = Neighbor(self, neighbor_ip, 120, boot_time, self.time_of_boot)

            if detected_via_non_sync_msg:
                self.neighbors[neighbor_ip].start_sync_process()

    def receive_hello(self, packet):
        ip = packet.ip_header.ip_src
        boot_time = packet.payload.boot_time
        print("ip = ", ip)
        options = packet.payload.payload.get_options()
        hello_hold_time = options["HOLDTIME"].holdtime
        checkpoint_sn = 0
        if "CHECKPOINT_SN" in options:
            checkpoint_sn = options["CHECKPOINT_SN"].checkpoint_sn
        with self.neighbors_lock:
            if ip in self.neighbors:
                self.neighbors[ip].recv_hello(boot_time, hello_hold_time, checkpoint_sn)
            else:
                self.new_neighbor(ip, boot_time, True)

    def receive_sync(self, packet):
        ip = packet.ip_header.ip_src
        boot_time = packet.payload.boot_time

        pkt_hs = packet.payload.payload  # type: PacketProtocolHelloSync

        # Process Sync msg
        my_boot_time = pkt_hs.neighbor_boot_time
        if my_boot_time != self.time_of_boot:
            return

        # All information in Sync msg
        sync_sn = pkt_hs.sync_sequence_number
        upstream_trees = pkt_hs.upstream_trees
        neighbor_sn = pkt_hs.my_snapshot_sn
        my_sn = pkt_hs.neighbor_snapshot_sn
        master_flag = pkt_hs.master_flag
        more_flag = pkt_hs.more_flag

        with self.neighbors_lock:
            if ip not in self.neighbors:
                self.new_neighbor(ip, boot_time, detected_via_non_sync_msg=False)

            self.neighbors[ip].recv_sync(upstream_trees, my_sn, neighbor_sn, boot_time, sync_sn, master_flag, more_flag, my_boot_time)

        return

    def receive_interest(self, packet):
        neighbor_source_ip = packet.ip_header.ip_src
        boot_time = packet.payload.boot_time

        pkt_jt = packet.payload.payload  # type: PacketProtocolInterest

        # Process Interest msg
        source_group = (pkt_jt.source, pkt_jt.group)
        sequence_number = pkt_jt.sequence_number

        # check neighbor existence
        with self.neighbors_lock:
            neighbor = self.neighbors.get(neighbor_source_ip, None)
            if neighbor is None:
                self.new_neighbor(neighbor_source_ip, boot_time)
                return

            try:
                if neighbor.recv_reliable_packet(sequence_number, source_group, boot_time):
                    if source_group not in neighbor.tree_metric_state:
                        neighbor.tree_state[source_group] = True
                        Main.kernel.recv_interest_msg(source_group, self)
                    else:
                        neighbor.tree_state[source_group] = True
                        #neighbor.tree_metric_state[source_group] = None
                        neighbor.tree_metric_state.pop(source_group, None)
                        Main.kernel.recv_install_or_uninstall_msg(source_group, self)
            except:
                traceback.print_exc()

    def receive_no_interest(self, packet):
        neighbor_source_ip = packet.ip_header.ip_src
        boot_time = packet.payload.boot_time

        pkt_jt = packet.payload.payload  # type: PacketProtocolNoInterest

        # Process NoInterest msg
        source_group = (pkt_jt.source, pkt_jt.group)
        sequence_number = pkt_jt.sequence_number

        # check neighbor existence
        with self.neighbors_lock:
            neighbor = self.neighbors.get(neighbor_source_ip, None)
            if neighbor is None:
                self.new_neighbor(neighbor_source_ip, boot_time)
                return

            try:
                if neighbor.recv_reliable_packet(sequence_number, source_group, boot_time):
                    if source_group not in neighbor.tree_metric_state:
                        neighbor.tree_state[source_group] = False
                        Main.kernel.recv_interest_msg(source_group, self)
                    else:
                        neighbor.tree_state[source_group] = False
                        #neighbor.tree_metric_state[source_group] = None
                        neighbor.tree_metric_state.pop(source_group, None)
                        Main.kernel.recv_install_or_uninstall_msg(source_group, self)
            except:
                traceback.print_exc()

    def receive_i_am_upstream(self, packet):
        from tree.metric import AssertMetric
        neighbor_source_ip = packet.ip_header.ip_src
        boot_time = packet.payload.boot_time
        pkt_jt = packet.payload.payload # type: PacketProtocolUpstream

        # Process IamUpstream msg
        source_group = (pkt_jt.source, pkt_jt.group)
        sequence_number = pkt_jt.sequence_number

        metric_preference = pkt_jt.metric_preference
        metric = pkt_jt.metric
        received_metric = AssertMetric(metric_preference=metric_preference, route_metric=metric, ip_address=neighbor_source_ip)

        # check neighbor existence
        with self.neighbors_lock:
            neighbor = self.neighbors.get(neighbor_source_ip, None)
            if neighbor is None:
                self.new_neighbor(neighbor_source_ip, boot_time)
                return

            try:
                if neighbor.recv_reliable_packet(sequence_number, source_group, boot_time):
                    #neighbor.tree_state[source_group] = False
                    neighbor.tree_state.pop(source_group, None)
                    neighbor.tree_metric_state[source_group] = received_metric
                    Main.kernel.recv_install_or_uninstall_msg(source_group, self)
            except:
                traceback.print_exc()

    def receive_i_am_no_longer_upstream(self, packet):
        neighbor_source_ip = packet.ip_header.ip_src
        boot_time = packet.payload.boot_time
        pkt_jt = packet.payload.payload

        # Process IamNoLongerUpstream msg
        source_group = (pkt_jt.source, pkt_jt.group)
        sequence_number = pkt_jt.sequence_number

        # check neighbor existence
        with self.neighbors_lock:
            neighbor = self.neighbors.get(neighbor_source_ip, None)
            if neighbor is None:
                self.new_neighbor(neighbor_source_ip, boot_time)
                return

            try:
                if neighbor.recv_reliable_packet(sequence_number, source_group, boot_time):
                    #neighbor.tree_state[source_group] = True
                    neighbor.tree_state.pop(source_group, None)
                    #neighbor.tree_metric_state[source_group] = None
                    neighbor.tree_metric_state.pop(source_group, None)
                    Main.kernel.recv_install_or_uninstall_msg(source_group, self)
            except:
                traceback.print_exc()


    def receive_ack(self, packet):
        neighbor_source_ip = packet.ip_header.ip_src
        neighbor_boot_time = packet.payload.boot_time
        pkt_ack = packet.payload.payload  # type: PacketProtocolAck

        # Process Ack msg
        source_group = (pkt_ack.source, pkt_ack.group)
        my_boot_time = pkt_ack.neighbor_boot_time
        my_snapshot_sn = pkt_ack.neighbor_snapshot_sn
        neighbor_snapshot_sn = pkt_ack.my_snapshot_sn
        sequence_number = pkt_ack.sequence_number

        print("RECEBI ACK")

        # check neighbor existence
        with self.neighbors_lock:
            neighbor = self.neighbors.get(neighbor_source_ip, None) # type: Neighbor
            if neighbor is None:
                self.new_neighbor(neighbor_source_ip, neighbor_boot_time)
                return

            with self.sequencer_lock:
                with self.reliable_transmission_lock:
                    if not neighbor.recv_ack(my_boot_time, neighbor_boot_time, my_snapshot_sn, neighbor_snapshot_sn):
                        return

                    #if my_boot_time != self.time_of_boot:
                    #    return

                    reliable_transmission = self.reliable_transmission_buffer.get(source_group, None)
                    if reliable_transmission is not None:
                        reliable_transmission.receive_ack(neighbor_source_ip, my_boot_time, sequence_number)


    PKT_FUNCTIONS = {
        PacketProtocolHello.PIM_TYPE:            receive_hello,
        PacketProtocolHelloSync.PIM_TYPE:        receive_sync,
        PacketProtocolUpstream.PIM_TYPE:         receive_i_am_upstream,
        PacketProtocolNoLongerUpstream.PIM_TYPE: receive_i_am_no_longer_upstream,
        PacketProtocolInterest.PIM_TYPE:         receive_interest,
        PacketProtocolNoInterest.PIM_TYPE:       receive_no_interest,
        PacketProtocolAck.PIM_TYPE:              receive_ack,
    }


    ########################################################################
    # Message Transmission
    ########################################################################
    def get_reliable_message_transmission(self, tree):
        with self.reliable_transmission_lock:
            reliable_msg_transmission = self.reliable_transmission_buffer.get(tree, None)

            if reliable_msg_transmission is None:
                reliable_msg_transmission = ReliableMessageTransmission(self)
                self.reliable_transmission_buffer[tree] = reliable_msg_transmission

            return reliable_msg_transmission

    def send_i_am_upstream(self, source, group, rpc):
        tree = (source, group)
        with self.sequencer_lock:
            with self.reliable_transmission_lock:
                self.get_reliable_message_transmission(tree).send_i_am_upstream(source, group, rpc)

    def send_i_am_no_longer_upstream(self, source, group):
        tree = (source, group)
        with self.sequencer_lock:
            with self.reliable_transmission_lock:
                self.get_reliable_message_transmission(tree).send_i_am_no_longer_upstream(source, group)

    def send_interest(self, source, group, dst):
        tree = (source, group)
        with self.sequencer_lock:
            with self.reliable_transmission_lock:
                self.get_reliable_message_transmission(tree).send_interest(source, group, dst)

    def send_no_interest(self, source, group, dst):
        tree = (source, group)
        with self.sequencer_lock:
            with self.reliable_transmission_lock:
                self.get_reliable_message_transmission(tree).send_no_interest(source, group, dst)

    def neighbor_start_synchronization(self, neighbor_ip, my_snapshot_bt, my_snapshot_sn):
        with self.reliable_transmission_lock:
            for rmt in self.reliable_transmission_buffer.values():
                rmt.receive_ack(neighbor_ip, my_snapshot_bt, my_snapshot_sn)

    def cancel_all_messages(self, tree):
        with self.reliable_transmission_lock:
            if tree in self.reliable_transmission_buffer:
                self.reliable_transmission_buffer[tree].cancel_all_messages()

    def cancel_interest_message(self, tree, neighbor_ip):
        with self.reliable_transmission_lock:
            if tree in self.reliable_transmission_buffer:
                self.reliable_transmission_buffer[tree].cancel_message_unicast(neighbor_ip)

    def cancel_upstream_message(self, tree):
        with self.reliable_transmission_lock:
            if tree in self.reliable_transmission_buffer:
                self.reliable_transmission_buffer[tree].cancel_message_multicast()

    def clear_reliable_transmission(self):
        with self.reliable_transmission_lock:
            for rmt in self.reliable_transmission_buffer.values():
                rmt.cancel_all_messages()

    '''
    def cancel_message(self, tree):
        with self.reliable_transmission_lock:
            reliable_packet = self.reliable_transmission_buffer.get(tree, None)
            if reliable_packet is not None:
                reliable_packet.cancel_message()
    '''
