from threading import Timer, RLock

class ReliableTransmission(object):
    TIMEOUT = 10
    DISPOSAL_TIMEOUT = 120

    def __init__(self, interface, packet, message_destination, neighbors_ips):
        self._lock = RLock()
        self._msg_was_delivered = False
        self._interface = interface
        self._msg = packet
        self._msg_dst = message_destination
        self._neighbors_that_should_ack = neighbors_ips
        self._neighbors_that_acked = set()
        self._timer = Timer(ReliableTransmission.TIMEOUT, self.timeout)
        self._timer.start()

        # timer to remove this message from reliable_msg_queue
        self._disposal_timer = Timer(ReliableTransmission.DISPOSAL_TIMEOUT, self.disposal_timeout)


    @property
    def id_reliable(self):
        return self._msg.payload.id_reliable

    def _check_if_message_was_delivered(self):
        with self._lock:
            if self._msg_was_delivered:
                return True
            self._msg_was_delivered = self._neighbors_that_should_ack <= self._neighbors_that_acked
            if self._msg_was_delivered:
                self.clear_timer()
                self._disposal_timer.start()
            return self._msg_was_delivered

    def timeout(self):
        with self._lock:
            if self._check_if_message_was_delivered():
                return

            # didnt received acks from every neighbor... so lets resend msg and reschedule timer
            self._interface.send(self._msg, self._msg_dst)
            self._timer = Timer(ReliableTransmission.TIMEOUT, self.timeout)
            self._timer.start()

    def disposal_timeout(self):
        # remove this msg from reliable transmission buffer... since everyone received this msg
        self._interface.reliable_transmission_buffer.pop(self.id_reliable)

    def clear_timer(self):
        with self._lock:
            self._timer.cancel()

    def receive_ack(self, neighbor_ip):
        with self._lock:
            if self._msg_was_delivered:
                return
            self._neighbors_that_acked.add(neighbor_ip)
            self._check_if_message_was_delivered()
