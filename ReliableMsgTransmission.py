from threading import Timer, RLock
from Packet.Packet import Packet
from tree.globals import MSG_FORMAT, MESSAGE_RETRANSMISSION_TIME
if MSG_FORMAT == "BINARY":
    from Packet.PacketProtocolHeader import PacketNewProtocolHeader as PacketProtocolHeader
    from Packet.PacketProtocolSetTree import PacketNewProtocolUpstream as PacketProtocolUpstream
    from Packet.PacketProtocolRemoveTree import PacketNewProtocolNoLongerUpstream as PacketProtocolNoLongerUpstream
    from Packet.PacketProtocolInterest import PacketNewProtocolInterest as PacketProtocolInterest
    from Packet.PacketProtocolInterest import PacketNewProtocolNoInterest as PacketProtocolNoInterest
else:
    from Packet.PacketProtocolHeader import PacketProtocolHeader
    from Packet.PacketProtocolSetTree import PacketProtocolUpstream
    from Packet.PacketProtocolRemoveTree import PacketProtocolNoLongerUpstream
    from Packet.PacketProtocolInterest import PacketProtocolInterest
    from Packet.PacketProtocolInterest import PacketProtocolNoInterest

'''
class ReliableTransmission(object):
    TIMEOUT = 10

    def __init__(self, interface, packet, message_destination=None):
        self._interface = interface
        self._msg = packet
        self._msg_dst = message_destination
        self._neighbors_that_acked = set()
        #self._retransmission_timer = Timer(ReliableTransmission.TIMEOUT, self.retransmission_timeout)
        #self._retransmission_timer.start()
        self._retransmission_timer = None
        self.retransmission_timeout()

    def receive_ack(self, neighbor_ip, sn):
        msg = self._msg
        dst = self._msg_dst

        if msg is not None and dst is None and sn == msg.payload.payload.sequence_number:
            # destination is multicast
            self._neighbors_that_acked.add(neighbor_ip)
            if self.did_all_neighbors_acked():
                self.message_has_been_reliably_transmitted()

        elif msg is not None and dst == neighbor_ip and sn == msg.payload.payload.sequence_number:
            # destination is unicast
            self.message_has_been_reliably_transmitted()

    def did_all_neighbors_acked(self):
        return self._interface.did_all_neighbors_acked(self._neighbors_that_acked)

    def message_has_been_reliably_transmitted(self):
        self.cancel_message()

    def cancel_message(self):
        self.clear_retransmission_timer()
        self._neighbors_that_acked.clear()

    ##########################################
    # Set timers
    ##########################################
    # Reliable timer
    def set_retransmission_timer(self):
        self.clear_retransmission_timer()
        self._retransmission_timer = Timer(ReliableTransmission.TIMEOUT, self.retransmission_timeout)
        self._retransmission_timer.start()

    def clear_retransmission_timer(self):
        if self._retransmission_timer is not None:
            self._retransmission_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def retransmission_timeout(self):
        if self._msg_dst is None and self.did_all_neighbors_acked():
            self.message_has_been_reliably_transmitted()
            return

        # didnt received acks from every neighbor... so lets resend msg and reschedule timer
        if self._msg_dst is None:
            self._interface.send(self._msg)
        else:
            self._interface.send(self._msg, self._msg_dst)
        self.set_retransmission_timer()

'''

class ReliableMessageTransmission(object):
    def __init__(self, interface):
        self._interface = interface
        self._msg_multicast = None
        self._msg_unicast = (None, None)
        self._neighbors_that_acked = set()
        self._retransmission_timer = None
        self._lock = RLock()


    def send_i_am_upstream(self, source, group, rpc):
        with self._lock:
            self.cancel_messsage_multicast()

            (bt, sn) = self._interface.get_sequence_number()

            metric_preference = rpc.metric_preference
            metric = rpc.route_metric

            ph = PacketProtocolUpstream(source, group, metric_preference, metric, sn)
            self._msg_multicast = Packet(payload=PacketProtocolHeader(ph, boot_time=bt))

            self.set_retransmission_timer()
            self._interface.send(self._msg_multicast)


    def send_i_am_no_longer_upstream(self, source, group):
        with self._lock:
            self.cancel_messsage_multicast()

            (bt, sn) = self._interface.get_sequence_number()

            ph = PacketProtocolNoLongerUpstream(source, group, sn)
            self._msg_multicast = Packet(payload=PacketProtocolHeader(ph, boot_time=bt))

            self.set_retransmission_timer()
            self._interface.send(self._msg_multicast)

    def send_interest(self, source, group, dst):
        with self._lock:
            self.cancel_message_unicast()

            (bt, sn) = self._interface.get_sequence_number()

            ph = PacketProtocolInterest(source, group, sn)
            self._msg_unicast = (Packet(payload=PacketProtocolHeader(ph, boot_time=bt)), dst)

            self.set_retransmission_timer()
            self._interface.send(*self._msg_unicast)

    def send_no_interest(self, source, group, dst):
        with self._lock:
            self.cancel_message_unicast()

            (bt, sn) = self._interface.get_sequence_number()

            ph = PacketProtocolNoInterest(source, group, sn)
            self._msg_unicast = (Packet(payload=PacketProtocolHeader(ph, boot_time=bt)), dst)

            self.set_retransmission_timer()
            self._interface.send(*self._msg_unicast)


    def receive_ack(self, neighbor_ip, bt, sn):
        with self._lock:
            msg = self._msg_multicast
            if msg is not None and (bt > msg.payload.boot_time or
                                    bt == msg.payload.boot_time and sn >= msg.payload.payload.sequence_number):
                self._neighbors_that_acked.add(neighbor_ip)
                if self.did_all_neighbors_acked():
                    #self.message_has_been_reliably_transmitted()
                    self.cancel_messsage_multicast()

            (msg, dst) = self._msg_unicast
            if msg is not None and dst == neighbor_ip and (bt > msg.payload.boot_time or
                                            bt == msg.payload.boot_time and sn >= msg.payload.payload.sequence_number):
                # destination is unicast
                #self.message_has_been_reliably_transmitted()
                self.cancel_message_unicast()

    def did_all_neighbors_acked(self):
        with self._lock:
            return self._interface.did_all_neighbors_acked(self._neighbors_that_acked)

    def cancel_messsage_multicast(self):
        with self._lock:
            self._neighbors_that_acked.clear()
            self._msg_multicast = None
            if self._msg_unicast is None:
                self.clear_retransmission_timer()

    def cancel_message_unicast(self):
        with self._lock:
            self._msg_unicast = (None, None)
            if self._msg_multicast is None:
                self.clear_retransmission_timer()

    def cancel_all_messages(self):
        with self._lock:
            self.clear_retransmission_timer()
            self._neighbors_that_acked.clear()
            self._msg_multicast = None
            self._msg_unicast = (None, None)

    ##########################################
    # Set timers
    ##########################################
    # Reliable timer
    def set_retransmission_timer(self):
        self.clear_retransmission_timer()
        self._retransmission_timer = Timer(MESSAGE_RETRANSMISSION_TIME, self.retransmission_timeout)
        self._retransmission_timer.start()

    def clear_retransmission_timer(self):
        if self._retransmission_timer is not None:
            self._retransmission_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def retransmission_timeout(self):
        with self._lock:
            # recheck if all neighbors acked
            if self._msg_multicast is not None and self.did_all_neighbors_acked():
                self.cancel_messsage_multicast()

            # didnt received acks from every neighbor... so lets resend msg and reschedule timer
            msg = self._msg_multicast
            if msg is not None:
                self._interface.send(msg)

            (msg, dst) = self._msg_unicast
            if msg is not None and dst is not None:
                self._interface.send(msg, dst)

            if self._msg_multicast is not None or self._msg_unicast[0] is not None:
                self.set_retransmission_timer()

    #############################################
    # Get Sequence Number for CheckpointSN
    #############################################
    def get_sequence_number(self):
        bt_sn = (None, None)
        with self._lock:
            msg = self._msg_multicast
            if msg is not None:
                bt_sn = (msg.payload.boot_time, msg.payload.payload.sequence_number)

            (msg, _) = self._msg_unicast
            if msg is not None and bt_sn[0] is None or\
                    msg is not None and bt_sn[0] is not None and bt_sn[0] <= msg.payload.boot_time and bt_sn[1] > msg.payload.payload.sequence_number:
                bt_sn = (msg.payload.boot_time, msg.payload.payload.sequence_number)

        return bt_sn
