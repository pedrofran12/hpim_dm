from threading import Timer
import time
from utils import HELLO_HOLD_TIME_NO_TIMEOUT, HELLO_HOLD_TIME_TIMEOUT, TYPE_CHECKING
from threading import Lock, RLock
if TYPE_CHECKING:
    from InterfaceProtocol import InterfaceProtocol


class Neighbor:
    RETRANSMISSION_TIMEOUT = 10
    GARBAGE_COLLECT_TIMEOUT = 120

    def __init__(self, contact_interface: "InterfaceProtocol", ip, generation_id: int, hello_hold_time: int):
        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            raise Exception
        self.contact_interface = contact_interface
        self.ip = ip
        self.generation_id = generation_id

        self.neighbor_liveness_timer = None
        self.hello_hold_time = None
        self.set_hello_hold_time(hello_hold_time)
        self.time_of_last_update = time.time()

        self.tree_interface_nlt_subscribers = []
        self.tree_interface_nlt_subscribers_lock = RLock()


        self.tree_state = {}
        self.tree_metric_state = {}

        self.minimum_sequence_number = 0
        self.last_sequence_number = {}



        #self.tree_timers = {}
        #self.tree_lock = RLock()
        #self.tree_packets_waiting_for_ack = {}



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
        interest_state = self.tree_state.get(tree, False)
        upstream_state = self.tree_metric_state.get(tree, None)
        return (interest_state, upstream_state)



    def recv_reliable_packet(self, sn, tree):
        from Packet.PacketProtocolAck import PacketProtocolAck
        from Packet.PacketProtocolHeader import PacketProtocolHeader
        from Packet.Packet import Packet

        # todo lock quando implementar timer
        last_received_sn = self.last_sequence_number.get(tree, 0)

        if sn < self.minimum_sequence_number:
            # dont deliver to application
            return False
        elif sn >= last_received_sn:
            (source, group) = tree
            ack = PacketProtocolAck(source, group, sn)
            ph = PacketProtocolHeader(ack)
            packet = Packet(payload=ph)
            self.contact_interface.send(packet, self.ip)

            # todo set timer
            if sn > last_received_sn:
                # update most recent sn received from this neighbor
                self.last_sequence_number[tree] = sn

                # deliver to application
                return True
        # dont deliver to application
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
        print('HELLO TIMER EXPIRED... remove neighbor')
        if self.neighbor_liveness_timer is not None:
            self.neighbor_liveness_timer.cancel()

        self.contact_interface.remove_neighbor(self.ip)

        # notify interfaces which have this neighbor as AssertWinner
        with self.tree_interface_nlt_subscribers_lock:
            for tree_if in self.tree_interface_nlt_subscribers:
                tree_if.assert_winner_nlt_expires()


    def reset(self):
        self.contact_interface.new_or_reset_neighbor(self.ip)


    def receive_hello(self, generation_id, hello_hold_time):
        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            self.set_hello_hold_time(hello_hold_time)
        else:
            self.time_of_last_update = time.time()
            self.set_generation_id(generation_id)
            self.set_hello_hold_time(hello_hold_time)


    def subscribe_nlt_expiration(self, tree_if):
        with self.tree_interface_nlt_subscribers_lock:
            if tree_if not in self.tree_interface_nlt_subscribers:
                self.tree_interface_nlt_subscribers.append(tree_if)

    def unsubscribe_nlt_expiration(self, tree_if):
        with self.tree_interface_nlt_subscribers_lock:
            if tree_if in self.tree_interface_nlt_subscribers:
                self.tree_interface_nlt_subscribers.remove(tree_if)
