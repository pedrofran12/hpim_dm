from threading import Timer, RLock
from hpimdm.tree.hpim_globals import MESSAGE_RETRANSMISSION_TIME, ACK_FAILURE_THRESHOLD


class ReliableMessageTransmission(object):
    def __init__(self, interface):
        self._interface = interface
        self._msg_multicast = None
        self._msg_unicast = {}
        self._neighbors_that_acked = set()
        self._number_of_failed_acks = {}
        self._retransmission_timer = None
        self._lock = RLock()

    def send_i_am_upstream(self, source, group, rpc):
        """
        Send reliably a new IamUpstream message
        """
        with self._lock:
            self.cancel_all_messages()

            (bt, sn) = self._interface.get_sequence_number()

            metric_preference = rpc.metric_preference
            metric = rpc.route_metric

            self._msg_multicast = self._interface.create_i_am_upstream_msg(my_boot_time=bt, sn=sn,
                                                                           source=source, group=group,
                                                                           metric_preference=metric_preference,
                                                                           metric=metric)

            self.set_retransmission_timer()
            self._interface.send(self._msg_multicast)

    def send_i_am_no_longer_upstream(self, source, group):
        """
        Send reliably a new IamNoLongerUpstream message
        """
        with self._lock:
            self.cancel_all_messages()

            (bt, sn) = self._interface.get_sequence_number()

            self._msg_multicast = self._interface.create_i_am_no_longer_upstream_msg(my_boot_time=bt, sn=sn,
                                                                                     source=source, group=group)

            self.set_retransmission_timer()
            self._interface.send(self._msg_multicast)

    def send_interest(self, source, group, dst):
        """
        Send reliably a new Interest message
        """
        with self._lock:
            self.cancel_message_unicast(dst)

            (bt, sn) = self._interface.get_sequence_number()

            packet = self._interface.create_interest_msg(my_boot_time=bt, sn=sn, source=source, group=group)
            self._msg_unicast[dst] = packet

            self.set_retransmission_timer()
            self._interface.send(packet, dst)

            # msg multicast doesnt require to be reliably protected to dst (because unicast msgs can only be transmitted
            # in concurrency with IamNoLongerUpstream - interest msg implies that neighbor is not Upstream... so dont
            # wait ack regarding multicast msg)
            if self._msg_multicast is not None:
                self._neighbors_that_acked.add(dst)

    def send_no_interest(self, source, group, dst):
        """
        Send reliably a new NoInterest message
        """
        with self._lock:
            self.cancel_message_unicast(dst)

            (bt, sn) = self._interface.get_sequence_number()

            packet = self._interface.create_no_interest_msg(my_boot_time=bt, sn=sn, source=source, group=group)
            self._msg_unicast[dst] = packet

            self.set_retransmission_timer()
            self._interface.send(packet, dst)

            # msg multicast doesnt require to be reliably protected to dst (because unicast msgs can only be transmitted
            # in concurrency with IamNoLongerUpstream - interest msg implies that neighbor is not Upstream... so dont
            # wait ack regarding multicast msg)
            if self._msg_multicast is not None:
                self._neighbors_that_acked.add(dst)

    def receive_ack(self, neighbor_ip, bt, sn):
        """
        Received Ack regarding this tree
        """
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
        """
        Verify if all known neighbors have acked a multicast message
        """
        with self._lock:
            return self._interface.did_all_neighbors_acked(self._neighbors_that_acked)

    def cancel_messsage_multicast(self):
        """
        Stop reliably monitoring an IamUpstream/IamNoLongerUpstream message
        """
        with self._lock:
            self._neighbors_that_acked.clear()
            self._msg_multicast = None
            if len(self._msg_unicast) == 0:
                # there are no multicast nor unicast messages being transmitted
                self.clear_retransmission_timer()
                self._number_of_failed_acks.clear()
            else:
                # only unicast messages are being transmitted
                neighbors_that_have_acked = self._number_of_failed_acks.keys() - self._msg_unicast.keys()
                for n in neighbors_that_have_acked:
                    self._number_of_failed_acks.pop(n, None)

    def cancel_message_unicast(self, ip):
        """
        Stop reliably monitoring an Interest/NoInterest message
        """
        with self._lock:
            self._msg_unicast.pop(ip, None)
            self._number_of_failed_acks.pop(ip, None)
            if self._msg_multicast is None and len(self._msg_unicast) == 0:
                self.clear_retransmission_timer()

    def cancel_all_messages(self):
        """
        Stop reliably monitoring any message regarding this tree
        (IamUpstream/IamNoLongerUpstream/Interest/NoInterest)
        """
        with self._lock:
            self.clear_retransmission_timer()
            self._neighbors_that_acked.clear()
            self._number_of_failed_acks.clear()
            self._msg_multicast = None
            self._msg_unicast.clear()

    ##########################################
    # Set timers
    ##########################################
    # Reliable timer
    def set_retransmission_timer(self):
        """
        Set retransmission timer used to control retransmission of control messages
        """
        self.clear_retransmission_timer()
        self._retransmission_timer = Timer(MESSAGE_RETRANSMISSION_TIME, self.retransmission_timeout)
        self._retransmission_timer.start()

    def clear_retransmission_timer(self):
        """
        Stop retransmission timer
        """
        if self._retransmission_timer is not None:
            self._retransmission_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def retransmission_timeout(self):
        """
        Retransmission timer has expired
        """
        neighbors_not_acked = set()
        with self._interface.neighbors_lock:
            with self._lock:
                # recheck if all neighbors acked
                if self._msg_multicast is not None and self.did_all_neighbors_acked():
                    self.cancel_messsage_multicast()
                elif self._msg_multicast is not None:
                    # take note of all neighbors that have not acked the multicast msg
                    neighbors_not_acked = self.get_interface_neighbors() - self._neighbors_that_acked

                # didnt received acks from every neighbor... so lets resend msg and reschedule timer
                msg = self._msg_multicast
                if msg is not None:
                    self._interface.send(msg)

                for (dst, msg) in self._msg_unicast.copy().items():
                    if self._interface.is_neighbor(dst):
                        self._interface.send(msg, dst)
                        neighbors_not_acked.add(dst)  # take note of all neighbors that have not acked unicast messages
                    else:
                        self.cancel_message_unicast(dst)

                if self._msg_multicast is not None or len(self._msg_unicast) > 0:
                    self.set_retransmission_timer()

                # update number of failed acks per neighbor and check which ones should be considered to have failed
                for neighbor_ip in neighbors_not_acked:
                    self._number_of_failed_acks[neighbor_ip] = self._number_of_failed_acks.get(neighbor_ip, 0) + 1
                self.check_neighbor_failures()

    #############################################
    # Get Sequence Number for CheckpointSN
    #############################################
    def get_sequence_number(self):
        """
        Get the lowest sequence number of a control message that is being currently reliably transmitted...
        This method will be used to determine the CheckpointSN to be transmitted in Hello messages
        """
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

    #############################################
    # Check neighbor failures
    # Force neighbor failure in case neighbor does not ack successive control messages
    #############################################
    def check_neighbor_failures(self):
        with self._lock:
            for (neighbor_ip, ack_failures) in self._number_of_failed_acks.copy().items():
                if ack_failures > ACK_FAILURE_THRESHOLD:
                    print("NEIGHBOR FAILED DUE TO ACK LACK: " + neighbor_ip)
                    self.force_neighbor_failure(neighbor_ip)

    def force_neighbor_failure(self, neighbor_ip):
        with self._lock:
            self._interface.force_neighbor_failure(neighbor_ip)
            self._number_of_failed_acks.pop(neighbor_ip, None)

    def get_interface_neighbors(self):
        return self._interface.get_neighbors_ip()
