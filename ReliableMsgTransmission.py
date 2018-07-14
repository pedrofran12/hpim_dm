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


class ReliableMessageTransmission(object):
    def __init__(self, interface):
        self._interface = interface
        self._msg_multicast = None
        self._msg_unicast = {}
        self._neighbors_that_acked = set()
        self._retransmission_timer = None
        self._lock = RLock()

    def send_i_am_upstream(self, source, group, rpc):
        with self._lock:
            self.cancel_all_messages()

            (bt, sn) = self._interface.get_sequence_number()

            metric_preference = rpc.metric_preference
            metric = rpc.route_metric

            ph = PacketProtocolUpstream(source, group, metric_preference, metric, sn)
            self._msg_multicast = Packet(payload=PacketProtocolHeader(ph, boot_time=bt))

            self.set_retransmission_timer()
            self._interface.send(self._msg_multicast)

    def send_i_am_no_longer_upstream(self, source, group):
        with self._lock:
            self.cancel_all_messages()

            (bt, sn) = self._interface.get_sequence_number()

            ph = PacketProtocolNoLongerUpstream(source, group, sn)
            self._msg_multicast = Packet(payload=PacketProtocolHeader(ph, boot_time=bt))

            self.set_retransmission_timer()
            self._interface.send(self._msg_multicast)

    def send_interest(self, source, group, dst):
        with self._lock:
            self.cancel_message_unicast(dst)

            (bt, sn) = self._interface.get_sequence_number()

            ph = PacketProtocolInterest(source, group, sn)
            self._msg_unicast[dst] = Packet(payload=PacketProtocolHeader(ph, boot_time=bt))

            self.set_retransmission_timer()
            self._interface.send(self._msg_unicast[dst], dst)

            # msg multicast doesnt require to be reliably protected to dst (because unicast msgs can only be transmitted
            # in concurrency with IamNoLongerUpstream - interest msg implies that neighbor is not Upstream... so dont
            # wait ack regarding multicast msg)
            if self._msg_multicast is not None:
                self._neighbors_that_acked.add(dst)

    def send_no_interest(self, source, group, dst):
        with self._lock:
            self.cancel_message_unicast(dst)

            (bt, sn) = self._interface.get_sequence_number()

            ph = PacketProtocolNoInterest(source, group, sn)
            self._msg_unicast[dst] = Packet(payload=PacketProtocolHeader(ph, boot_time=bt))

            self.set_retransmission_timer()
            self._interface.send(self._msg_unicast[dst], dst)

            # msg multicast doesnt require to be reliably protected to dst (because unicast msgs can only be transmitted
            # in concurrency with IamNoLongerUpstream - interest msg implies that neighbor is not Upstream... so dont
            # wait ack regarding multicast msg)
            if self._msg_multicast is not None:
                self._neighbors_that_acked.add(dst)

    def receive_ack(self, neighbor_ip, bt, sn):
        with self._lock:
            msg = self._msg_multicast
            if msg is not None and (bt > msg.payload.boot_time or
                                    bt == msg.payload.boot_time and sn >= msg.payload.payload.sequence_number):
                self._neighbors_that_acked.add(neighbor_ip)
                if self.did_all_neighbors_acked():
                    self.cancel_messsage_multicast()

            if neighbor_ip in self._msg_unicast:
                msg = self._msg_unicast[neighbor_ip]
                if bt > msg.payload.boot_time or (bt == msg.payload.boot_time and
                                                  sn >= msg.payload.payload.sequence_number):
                    self.cancel_message_unicast(neighbor_ip)

    def did_all_neighbors_acked(self):
        with self._lock:
            return self._interface.did_all_neighbors_acked(self._neighbors_that_acked)

    def cancel_messsage_multicast(self):
        with self._lock:
            self._neighbors_that_acked.clear()
            self._msg_multicast = None
            if len(self._msg_unicast) == 0:
                self.clear_retransmission_timer()

    def cancel_message_unicast(self, ip):
        with self._lock:
            self._msg_unicast.pop(ip, None)
            if self._msg_multicast is None and len(self._msg_unicast) == 0:
                self.clear_retransmission_timer()

    def cancel_all_messages(self):
        with self._lock:
            self.clear_retransmission_timer()
            self._neighbors_that_acked.clear()
            self._msg_multicast = None
            self._msg_unicast.clear()

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

            for (dst, msg) in self._msg_unicast.copy().items():
                if self._interface.is_neighbor(dst):
                    self._interface.send(msg, dst)
                else:
                    self.cancel_message_unicast(dst)

            if self._msg_multicast is not None or len(self._msg_unicast) > 0:
                self.set_retransmission_timer()

    #############################################
    # Get Sequence Number for CheckpointSN
    #############################################
    def get_sequence_number(self):
        bt_sn = (None, None)
        with self._lock:
            msg = self._msg_multicast
            if msg is not None:
                bt_sn = (msg.payload.boot_time, msg.payload.payload.sequence_number - 1)

            for (_, msg) in self._msg_unicast.items():
                if bt_sn[0] is None or bt_sn[0] is not None and \
                        (bt_sn[0] < msg.payload.boot_time or
                         bt_sn[0] == msg.payload.boot_time and bt_sn[1] > (msg.payload.payload.sequence_number - 1)):
                    bt_sn = (msg.payload.boot_time, msg.payload.payload.sequence_number - 1)
        return bt_sn
