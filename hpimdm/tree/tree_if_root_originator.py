import logging
import traceback
from threading import Timer
from threading import Thread

from . import data_packets_socket
from .hpim_globals import SOURCE_LIFETIME
from .tree_interface import TreeInterface


class TreeInterfaceRootOriginator(TreeInterface):
    LOGGER = logging.getLogger('hpim.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, current_tree_state):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = kernel_entry.get_interface_name(interface_id)
        logger = logging.LoggerAdapter(TreeInterfaceRootOriginator.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, None, current_tree_state, logger)

        # Originator state
        self._source_active_timer = None
        self.set_source_active_timer()

        # TODO TESTE SOCKET RECV DATA PCKTS
        self.socket_is_enabled = True
        (s, g) = self.get_tree_id()
        interface_name = self.get_interface_name()
        self.socket_pkt = data_packets_socket.get_s_g_bpf_filter_code(s, g, interface_name)

        # run receive method in background
        receive_thread = Thread(target=self.socket_recv)
        receive_thread.daemon = True
        receive_thread.start()

        self.logger.debug('Created RootInterfaceOriginator')

    def socket_recv(self):
        """
        Socket used to receive data packets from the Root interface...
        Useful in order to control the tree state of Originator routers
        """
        while self.socket_is_enabled:
            try:
                self.socket_pkt.recvfrom(0)
                print("DATA RECEIVED")
                self.recv_data_msg()
            except:
                traceback.print_exc()
                continue
        print("EXIT SOCKET")

    ##########################################
    # Set timers
    ##########################################
    # Originator timers
    def set_source_active_timer(self):
        """
        Set Source Active timer
        """
        self.clear_source_active_timer()
        self._source_active_timer = Timer(SOURCE_LIFETIME, self.source_active_timeout)
        self._source_active_timer.start()

    def clear_source_active_timer(self):
        """
        Stop Source Active timer
        """
        if self._source_active_timer is not None:
            self._source_active_timer.cancel()


    ###########################################
    # Timer timeout
    ###########################################
    def source_active_timeout(self):
        """
        Source Active timer expired... react to this event
        """
        self._kernel_entry.sat_expires()

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        """
        Root interface received data packet
        """
        if not self.is_tree_inactive():
            self.set_source_active_timer()
            if self.is_tree_unsure():
                self._kernel_entry.sat_running()

    ###########################################
    # Change to in/out-tree
    ###########################################
    def node_is_out_tree(self):
        return

    def node_is_in_tree(self):
        return

    ####################################################################
    def is_forwarding(self):
        """
        This interface must not be included in the OIL of the multicast routing table, thus returning False
        """
        return False

    def delete(self):
        """
        Tree interface is being removed... due to change of interface roles or
        due to the removal of the tree by this router
        Clear all state from this interface regarding this tree
        """
        self.socket_is_enabled = False
        try:
            from socket import SHUT_RDWR
            self.socket_pkt.shutdown(SHUT_RDWR)
        except:
            pass
        self.socket_pkt.close()
        super().delete()
        self.clear_source_active_timer()
        self._source_active_timer = None
