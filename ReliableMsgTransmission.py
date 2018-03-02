from threading import Timer

class ReliableTransmission(object):
    TIMEOUT = 5

    def __init__(self, interface, msg, neighbors):
        self._interface = interface
        self._msg = msg
        self._neighbors_that_should_ack = neighbors
        self._neighbors_that_acked = []
        self._timer = Timer(ReliableTransmission.TIMEOUT, self.timeout)

    def timeout(self):
        self._timer = Timer(ReliableTransmission.TIMEOUT, self.timeout)

    def clear_timer(self):
        self._timer.cancel()

    def receive_ack(self, neighbor_ip):
        if neighbor_ip in self._neighbors_that_should_ack:
            return
        if neighbor_ip not in self._neighbors_that_acked:
            self._neighbors_that_acked.append(neighbor_ip)
            if len(self._neighbors_that_should_ack) == len(self._neighbors_that_acked):
                # TODO remover interface
                self._interface.reliable_transmission_buffer.
                #self._interface.
                return