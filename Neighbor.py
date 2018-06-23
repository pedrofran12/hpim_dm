from threading import Timer
import time
from utils import HELLO_HOLD_TIME_NO_TIMEOUT, HELLO_HOLD_TIME_TIMEOUT, TYPE_CHECKING
from Packet.PacketProtocolAck import PacketProtocolAck
from Packet.PacketProtocolHelloSync import *
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet

from threading import Lock, RLock
if TYPE_CHECKING:
    from InterfaceProtocol import InterfaceProtocol


class NeighborState():
    @staticmethod
    def new_neighbor_or_adjacency_reset(neighbor):
        print("NEW NEIG")
        neighbor.set_sync_state(Slave)

        neighbor.start_snapshot()

        # Remove all info from neighbor (if already knew it)
        neighbor.tree_state.clear()
        neighbor.tree_metric_state.clear()
        neighbor.last_sequence_number.clear()
        neighbor.current_sync_sn = 0
        neighbor.minimum_sequence_number = 0
        #

        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[0:5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > 0
        my_snapshot_sn = neighbor.my_snapshot_sequencer

        from Packet.PacketProtocolSync import PacketProtocolHelloSync
        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, 0,
                                        sync_sequence_number=neighbor.current_sync_sn,
                                        upstream_trees=my_snapshot_mrt, master_flag=True,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.contact_interface.time_of_boot))
        neighbor.contact_interface.send(pkt, neighbor.ip)
        neighbor.set_sync_timer()

    @staticmethod
    def recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        return

    @staticmethod
    def sync_timer_expires(neighbor):
        return


class Updated(NeighborState):
    @staticmethod
    def recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.minimum_sequence_number > neighbor_snapshot_sn:
            return
        elif neighbor.minimum_sequence_number < neighbor_snapshot_sn:
            Updated.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            return

        if master_bit and (sync_sn > 1 and neighbor.my_snapshot_sequencer == my_snapshot_sn or sync_sn==0):
            from Packet.PacketProtocolSync import PacketProtocolHelloSync
            pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_snapshot_sn, sync_sequence_number=sync_sn,
                                            master_flag=False, more_flag=False, neighbor_boot_time=neighbor.time_of_boot)
            pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.contact_interface.time_of_boot))
            neighbor.contact_interface.send(pkt, neighbor.ip)


class Master(NeighborState):
    @staticmethod
    def recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.current_sync_sn == 0 and neighbor.minimum_sequence_number == 0:
            neighbor.minimum_sequence_number = neighbor_snapshot_sn

        if sync_sn != neighbor.current_sync_sn:
            print("EXIT MASTER")
            return

        if neighbor.minimum_sequence_number > neighbor_snapshot_sn:
            return
        elif neighbor.minimum_sequence_number < neighbor_snapshot_sn:
            Master.new_neighbor_or_adjacency_reset(neighbor)
            return

        if master_bit and (sync_sn > 0 and neighbor.my_snapshot_sequencer == my_snapshot_sn or sync_sn == 0):
            print("ENTROU MASTER")
            neighbor.install_tree_state(tree_state)

            my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn*5:(neighbor.current_sync_sn+1)*5]
            my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5
            my_snapshot_sn = neighbor.my_snapshot_sequencer
            neighbor_sn = neighbor.minimum_sequence_number

            from Packet.PacketProtocolSync import PacketProtocolHelloSync
            pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                            sync_sequence_number=neighbor.current_sync_sn,
                                            upstream_trees=my_snapshot_mrt, master_flag=False,
                                            more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
            pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.contact_interface.time_of_boot))
            neighbor.contact_interface.send(pkt, neighbor.ip)

            if not more_bit and not my_more_bit:
                neighbor.set_sync_state(Updated)
                neighbor.clear_sync_timer()
            else:
                neighbor.set_sync_timer()
                neighbor.current_sync_sn += 1

    @staticmethod
    def sync_timer_expires(neighbor):
        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[(neighbor.current_sync_sn - 1) * 5:
                                                                       neighbor.current_sync_sn * 5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > (neighbor.current_sync_sn - 1) * 5
        my_snapshot_sn = neighbor.my_snapshot_sequencer
        neighbor_sn = neighbor.minimum_sequence_number

        from Packet.PacketProtocolSync import PacketProtocolHelloSync
        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                        sync_sequence_number=neighbor.current_sync_sn - 1,
                                        upstream_trees=my_snapshot_mrt, master_flag=False,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.contact_interface.time_of_boot))
        neighbor.contact_interface.send(pkt, neighbor.ip)
        neighbor.set_sync_timer()


class Slave(NeighborState):
    @staticmethod
    def recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.current_sync_sn == 0 and neighbor.minimum_sequence_number == 0:
            neighbor.minimum_sequence_number = neighbor_snapshot_sn

        if neighbor.minimum_sequence_number > neighbor_snapshot_sn:
            return
        elif neighbor.minimum_sequence_number < neighbor_snapshot_sn:
            Slave.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            return

        if sync_sn == 0 and master_bit:
            print("HERE1")
            import ipaddress
            my_ip = ipaddress.ip_address(neighbor.contact_interface.get_ip())
            neighbor_ip = ipaddress.ip_address(neighbor.ip)
            if my_ip < neighbor_ip:
                print("HERE2")
                neighbor.set_sync_state(Master)
                neighbor.current_sync_sn = 0
                Master.recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit)
                return
        elif not master_bit and neighbor.my_snapshot_sequencer == my_snapshot_sn:
            print("HERE3")
            my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5

            if not my_more_bit and not more_bit:
                print("HERE4")
                neighbor.set_sync_state(Updated)
                neighbor.clear_sync_timer()
            else:
                print("HERE5")
                neighbor.current_sync_sn += 1
                neighbor.install_tree_state(tree_state)

                my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn*5:(neighbor.current_sync_sn+1)*5]
                my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5
                my_snapshot_sn = neighbor.my_snapshot_sequencer
                neighbor_sn = neighbor.minimum_sequence_number

                from Packet.PacketProtocolSync import PacketProtocolHelloSync
                pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                                sync_sequence_number=neighbor.current_sync_sn,
                                                upstream_trees=my_snapshot_mrt, master_flag=True,
                                                more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
                pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.contact_interface.time_of_boot))
                neighbor.contact_interface.send(pkt, neighbor.ip)
                neighbor.set_sync_timer()

    @staticmethod
    def sync_timer_expires(neighbor):
        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[
                          neighbor.current_sync_sn * 5:(neighbor.current_sync_sn + 1) * 5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn * 5
        my_snapshot_sn = neighbor.my_snapshot_sequencer
        neighbor_sn = neighbor.minimum_sequence_number

        from Packet.PacketProtocolSync import PacketProtocolHelloSync
        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                        sync_sequence_number=neighbor.current_sync_sn,
                                        upstream_trees=my_snapshot_mrt, master_flag=True,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.contact_interface.time_of_boot))
        neighbor.contact_interface.send(pkt, neighbor.ip)
        neighbor.set_sync_timer()


class Unknown(NeighborState):
    @staticmethod
    def recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if sync_sn == 0 and sync_sn == neighbor.current_sync_sn and master_bit:
            neighbor.set_sync_state(Master)

            neighbor.start_snapshot()

            # Remove all info from neighbor (if already knew it)
            neighbor.tree_state.clear()
            neighbor.tree_metric_state.clear()
            neighbor.last_sequence_number.clear()
            neighbor.current_sync_sn = 0
            neighbor.minimum_sequence_number = 0
            #

            Master.recv_hello_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit)
        else:
            Unknown.new_neighbor_or_adjacency_reset(neighbor)


class Neighbor:
    RETRANSMISSION_TIMEOUT = 10
    GARBAGE_COLLECT_TIMEOUT = 120

    def __init__(self, contact_interface: "InterfaceProtocol", ip, hello_hold_time: int, neighbor_time_of_boot=0):
        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            raise Exception
        self.contact_interface = contact_interface
        self.ip = ip
        #self.generation_id = generation_id
        self.time_of_boot = neighbor_time_of_boot

        self.neighbor_liveness_timer = None
        self.hello_hold_time = None
        self.set_hello_hold_time(hello_hold_time)
        self.time_of_last_update = time.time()

        self.current_sync_sn = 0
        self.my_last_msg = None

        # Tree Database storage
        self.tree_state = {}
        self.tree_metric_state = {}

        # Control if received control packets should be processed
        # Used to detect msg retransmissions and out of order reception
        self.minimum_sequence_number = 0
        self.last_sequence_number = {}

        self.sync_timer = None
        self.neighbor_state = Unknown

        #(my_snapshot_sn, my_snapshot_mrt) = contact_interface.snapshot_multicast_routing_table()
        #self.my_snapshot_sequencer = my_snapshot_sn # TODO
        #self.my_snapshot_multicast_routing_table = my_snapshot_mrt.values() # TODO
        #self.my_snapshot_trees = my_snapshot_mrt.keys() # TODO
        self.my_snapshot_sequencer = 0
        self.my_snapshot_multicast_routing_table = []
        self.my_snapshot_trees = []

        #self.tree_timers = {}
        #self.tree_lock = RLock()
        #self.tree_packets_waiting_for_ack = {}

    ######################################################################
    # Sync Timer
    ######################################################################
    def set_sync_timer(self):
        self.clear_sync_timer()
        self.sync_timer = Timer(10, self.sync_timeout)
        self.sync_timer.start()

    def clear_sync_timer(self):
        if self.sync_timer is not None:
            self.sync_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def sync_timeout(self):
        self.neighbor_state.sync_timer_expires(self)

    ############################################
    # Sync State
    ############################################
    def set_sync_state(self, state):
        if self.neighbor_state == state:
            return

        self.neighbor_state = state
        if state == Updated:
            import Main
            #Main.kernel.recv_ack_sync(self.ip, self.my_snapshot_trees, self.my_snapshot_sequencer, self.contact_interface)
            self.contact_interface.neighbor_finished_syncrhonization(self.ip, self.my_snapshot_sequencer)
            Main.kernel.recheck_all_trees(self.contact_interface)
            self.contact_interface.set_are_synchronizing()
            # inform about ack... nao sei se é aqui
        else:
            self.contact_interface.set_are_synchronizing()


    def install_tree_state(self, tree_state:list):
        #self.tree_state.clear()
        #self.tree_metric_state.clear()
        #self.last_sequence_number.clear()
        for t in tree_state:
            from tree.metric import AssertMetric
            tree_id = (t.source, t.group)
            self.tree_metric_state[tree_id] = AssertMetric(metric_preference=t.metric_preference, route_metric=t.metric, ip_address=self.ip)

    def get_known_trees(self):
        a = set(self.tree_metric_state.keys())
        b = set(self.tree_state.keys())
        return a.union(b)

    def is_syncing(self):
        return self.neighbor_state == Slave or self.neighbor_state == Master


    ######################################################################
    # Receive Synchronization Messages
    ######################################################################
    def start_sync_process(self, new_neighbor=False):
        #self.start_snapshot()

        #self.tree_state.clear()
        #self.tree_metric_state.clear()
        #self.last_sequence_number.clear()

        #self.current_sync_sn = 0

        self.neighbor_state.new_neighbor_or_adjacency_reset(self)

    def start_snapshot(self):
        (my_snapshot_sn, my_snapshot_mrt) = self.contact_interface.snapshot_multicast_routing_table()
        self.my_snapshot_sequencer = my_snapshot_sn
        self.my_snapshot_multicast_routing_table = list(my_snapshot_mrt.values())
        self.my_snapshot_trees = list(my_snapshot_mrt.keys())

    def recv_hello(self, boot_time, holdtime):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)

        self.set_hello_hold_time(holdtime)

    def recv_hello_sync(self, upstream_trees, my_sn, neighbor_sn, boot_time, sync_sn, master_flag, more_flag):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            #self.start_sync_process(True)
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            return

        '''
        if self.minimum_sequence_number == 0:
            self.minimum_sequence_number = neighbor_sn
        elif self.minimum_sequence_number != 0 and neighbor_sn > self.minimum_sequence_number:
            self.minimum_sequence_number = neighbor_sn
            #self.start_sync_process(True)
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)
        '''

        self.neighbor_state.recv_hello_sync(self, upstream_trees, my_sn, neighbor_sn, sync_sn, master_flag, more_flag)




        ##############
        '''
        if my_sn!=0 and my_sn!=self.my_snapshot_sequencer:
            return

        elif my_sn==0 and self.current_sync_sn==0 or my_sn==self.my_snapshot_sequencer:
            self.neighbor_state.recv_hello_sync(self, upstream_trees, sync_sn, master_flag, more_flag)


        ##################

        

        if my_sn!=0 and my_sn!=self.my_snapshot_sequencer:
            print("EXIT HERE")
            return


        if my_sn==0 and master_flag and not finish_flag and sync_sn==1 and self.current_sync_sn==1:
            print("FIRST")
            self.neighbor_state.recv_hello_sync_with_neigh_msn_is_zero_and_master_bit_set_and_finish_bit_unset_and_syncsn_is_1_and_current_sync_sn_is_1(self, more_flag, upstream_trees)
        elif not master_flag and not finish_flag:
            print("SECOND")
            self.neighbor_state.recv_hello_sync_with_master_bit_unset_and_finish_bit_unset(self, sync_sn, more_flag, upstream_trees)
        elif master_flag and not finish_flag:
            print("THIRD")
            self.neighbor_state.recv_hello_sync_with_master_bit_set_and_finish_bit_unset(self, sync_sn, more_flag, upstream_trees)
        elif master_flag and finish_flag:
            print("FOURTH")
            self.neighbor_state.recv_hello_sync_with_master_bit_set_and_finish_bit_set(self, sync_sn, more_flag, upstream_trees)
        elif not master_flag and finish_flag:
            print("FITH")
            self.neighbor_state.recv_hello_sync_with_master_bit_unset_and_finish_bit_set(self, sync_sn, more_flag)
        else:
            print("ELSE")
        
        ###
        if my_sn == self.my_snapshot_sequencer and neighbor_sn == self.minimum_sequence_number:
            self.neighbor_state.recv_hello_sync(self, upstream_trees)
        elif neighbor_sn > self.minimum_sequence_number:
            self.start_sync_process()
        ###
        '''
    '''
    def recv_hello_sync_ack(self, upstream_trees, my_sn, neighbor_sn, boot_time):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            self.start_sync_process(True)


        print("MY SNAPSHOT SN: ", self.my_snapshot_sequencer)
        print("NEIGHBOR SNAPSHOT SN: ", self.minimum_sequence_number)
        print("RCV MY SNAPSHOT SN:", my_sn)
        print("RCV NGH SNAPSHOT SN:", neighbor_sn)

        if my_sn == self.my_snapshot_sequencer and (self.minimum_sequence_number == 0 or self.minimum_sequence_number == neighbor_sn):
            print("AQUI AQUI AQUI")
            self.minimum_sequence_number = neighbor_sn
            self.neighbor_state.recv_hello_sync_ack(self, upstream_trees)
        elif my_sn == self.my_snapshot_sequencer and neighbor_sn > self.minimum_sequence_number:
            self.minimum_sequence_number = neighbor_sn
            #self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            self.start_sync_process()
    '''



    '''
    if my_sn == self.my_snapshot_sequencer and neighbor_sn == self.minimum_sequence_number:
        self.neighbor_state.recv_hello_sync_ack(self, upstream_trees)
    elif neighbor_sn > self.minimum_sequence_number:
        self.start_sync_process()
    '''
    '''
    def recv_hello_sync_ack_ack(self, my_sn, neighbor_sn, boot_time):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            self.start_sync_process()


        if my_sn == self.my_snapshot_sequencer and neighbor_sn == self.minimum_sequence_number:
            self.neighbor_state.recv_hello_sync_ack_ack(self)
        elif my_sn == self.my_snapshot_sequencer and neighbor_sn > self.minimum_sequence_number:
            self.minimum_sequence_number = neighbor_sn
            #self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            self.start_sync_process()
    '''
    '''
    if my_sn == self.my_snapshot_sequencer and neighbor_sn == self.minimum_sequence_number:
        self.neighbor_state.recv_hello_sync_ack_ack(self)
    elif neighbor_sn > self.minimum_sequence_number:
        self.start_sync_process()
    '''
    #######################################################################
    # Abstraction to Reliably Send Packets
    #######################################################################
    '''
    def send_tree_reliably(self, packet, sequence_number, source_group_pair):
        with self.tree_lock:
            if source_group_pair in self.tree_packets_waiting_for_ack:
                self.tree_packets_waiting_for_ack.pop(source_group_pair)


            retransmission_timer = Timer(Neighbor.RETRANSMISSION_TIMEOUT, self.retransmit_tree_packet, [source_group_pair, sequence_number])
            self.tree_packets_waiting_for_ack[source_group_pair] = [packet, sequence_number, retransmission_timer]

            retransmission_timer.start()
            self.contact_interface.send(packet, self.ip)

    def retransmit_tree_packet(self, source_group_pair, sequence_number):
        with self.tree_lock:
            if source_group_pair not in self.tree_packets_waiting_for_ack:
                return

            [packet, sequence_number_to_ack, retransmission_timer] = self.tree_packets_waiting_for_ack[source_group_pair]
            if sequence_number_to_ack < sequence_number:
                return

            retransmission_timer = Timer(Neighbor.RETRANSMISSION_TIMEOUT, self.retransmit_tree_packet, [source_group_pair, sequence_number])
            self.tree_packets_waiting_for_ack[source_group_pair] = [packet, sequence_number, retransmission_timer]

            retransmission_timer.start()
            self.contact_interface.send(packet, self.ip)

    def recv_tree_ack(self, source_group_pair, sequence_number):
        with self.tree_lock:
            if source_group_pair not in self.tree_packets_waiting_for_ack:
                return

            [_, waiting_ack_sn, retransmission_timer] = self.tree_packets_waiting_for_ack[source_group_pair]
            if waiting_ack_sn == sequence_number:
                self.tree_packets_waiting_for_ack.pop(source_group_pair)
                retransmission_timer.cancel()


    #######################################################################
    # Abstraction to Reliably Receive Packets
    #######################################################################
    def recv_reliable_packet(self, sequence_number, state, tree, source_of_message, message_is_install_type=False, metric_state=None):
        if sequence_number < self.minimum_sequence_number:
            return False

        (tree_source, tree_group) = tree
        if tree in self.tree_sequence_numbers and sequence_number < self.tree_sequence_numbers[tree]:
            return False

        # send ack to source_ip
        from Packet.PacketProtocolAck import PacketProtocolAck
        from Packet.PacketProtocolHeader import PacketProtocolHeader
        from Packet.Packet import Packet
        ph = PacketProtocolAck(tree_source, tree_group, sequence_number)
        pckt = Packet(payload=PacketProtocolHeader(ph))
        self.contact_interface.send(pckt, source_of_message)

        if tree in self.tree_timers:
            self.tree_timers[tree].cancel()
        self.tree_timers[tree] = Timer(Neighbor.GARBAGE_COLLECT_TIMEOUT, self.clean_reliable_timer, [tree, sequence_number])
        self.tree_timers[tree].start()

        # check if I already have the sequence_number updated
        if sequence_number == self.tree_sequence_numbers[tree]:
            # if I already know this sequence number stop here... dont deliver to application
            return False

        # otherwise I need to update sequence_number and deliver message information to protocol
        self.tree_sequence_numbers[tree] = sequence_number
        self.tree_state[tree] = state
        if message_is_install_type and metric_state is not None:
            self.tree_metric_state[tree] = metric_state
        else:
            self.tree_metric_state.pop(tree)

        # notify protocol about change
        return True

    def clean_reliable_timer(self, source_group_pair, sequence_number):
        if source_group_pair not in self.tree_sequence_numbers:
            return
        elif sequence_number != self.tree_sequence_numbers[source_group_pair]:
            return
        else:
            self.tree_sequence_numbers.pop(source_group_pair)
            self.tree_timers.pop(source_group_pair).cancel()
    


    #########################################
    def is_interested(self, tree):
        if tree in self.tree_state and self.tree_state[tree] == 'I':
            return True
        else:
            return False

    def get_metric_state(self, tree):
        return self.tree_metric_state.get(tree, None)

    
    #########################################
    '''
    ################################################################################################
    def get_tree_state(self, tree):
        if self.neighbor_state != Updated:
            return (False, None)
        else:
            upstream_state = self.tree_metric_state.get(tree, None)
            interest_state = False
            if upstream_state is None:
                interest_state = self.tree_state.get(tree, True)
            print("INTEREST NEIGHBOR ", self.ip, ":", interest_state)
            print("UPSTREAM NEIGHBOR ", self.ip, ":", upstream_state)
            return (interest_state, upstream_state)

    def recv_reliable_packet(self, sn, tree, boot_time):
        if self.neighbor_state != Updated:
            # do not interpret message during sync
            return False

        if boot_time < self.time_of_boot:
            return False
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            self.start_sync_process(new_neighbor=True)
            return False

        # todo lock quando implementar timer
        last_received_sn = self.last_sequence_number.get(tree, 0)

        if sn < self.minimum_sequence_number:
            # dont deliver to application
            print("RCVD ", sn)
            print("MSN ", self.minimum_sequence_number)

            return False
        elif sn >= last_received_sn:
            (source, group) = tree
            ack = PacketProtocolAck(source, group, sn, boot_time)
            ph = PacketProtocolHeader(ack, boot_time=self.contact_interface.time_of_boot)
            packet = Packet(payload=ph)
            self.contact_interface.send(packet, self.ip)

            # todo set timer
            if sn > last_received_sn:
                # update most recent sn received from this neighbor
                self.last_sequence_number[tree] = sn

                # deliver to application
                return True
        # dont deliver to application

        print("RCVD ", sn)
        print("LAST TREE SN ", last_received_sn)
        return False

    ################################################################################################

    def set_hello_hold_time(self, hello_hold_time: int):
        self.hello_hold_time = hello_hold_time
        if self.neighbor_liveness_timer is not None:
            self.neighbor_liveness_timer.cancel()

        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            self.remove()
        elif hello_hold_time != HELLO_HOLD_TIME_NO_TIMEOUT:
            self.neighbor_liveness_timer = Timer(hello_hold_time, self.remove)
            self.neighbor_liveness_timer.start()
        else:
            self.neighbor_liveness_timer = None

    def set_generation_id(self, generation_id):
        # neighbor restarted
        if self.generation_id != generation_id:
            self.generation_id = generation_id
            self.contact_interface.force_send_hello()
            self.reset()


    def remove(self):
        with self.contact_interface.neighbors_lock:
            print('HELLO TIMER EXPIRED... remove neighbor')
            if self.neighbor_liveness_timer is not None:
                self.neighbor_liveness_timer.cancel()

            self.clear_sync_timer()

            self.tree_state.clear()
            self.tree_metric_state.clear()
            self.last_sequence_number.clear()

            self.contact_interface.remove_neighbor(self.ip)

        '''
        # notify interfaces which have this neighbor as AssertWinner
        with self.tree_interface_nlt_subscribers_lock:
            for tree_if in self.tree_interface_nlt_subscribers:
                tree_if.assert_winner_nlt_expires()
        '''

    def reset(self):
        '''
        self.contact_interface.new_or_reset_neighbor(self.ip)
        '''
        return

    def receive_hello(self, generation_id, hello_hold_time):
        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            self.set_hello_hold_time(hello_hold_time)
        else:
            self.time_of_last_update = time.time()
            self.set_generation_id(generation_id)
            self.set_hello_hold_time(hello_hold_time)
