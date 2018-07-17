from .tree_interface import TreeInterface
from threading import Timer
from .globals import *
import traceback
from . import DataPacketsSocket
import threading
import logging
import Main


class TreeInterfaceUpstreamOriginator(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, best_upstream_router, current_tree_state):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceUpstreamOriginator.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, current_tree_state, logger)

        # Originator state
        self._source_active_timer = None
        if self.is_S_directly_conn():
            self.set_source_active_timer()

        # TODO TESTE SOCKET RECV DATA PCKTS
        self.socket_is_enabled = True
        (s, g) = self.get_tree_id()
        interface_name = self.get_interface_name()
        self.socket_pkt = DataPacketsSocket.get_s_g_bpf_filter_code(s, g, interface_name)

        # run receive method in background
        receive_thread = threading.Thread(target=self.socket_recv)
        receive_thread.daemon = True
        receive_thread.start()

        self.logger.debug('Created UpstreamInterface')


    def socket_recv(self):
        while self.socket_is_enabled:
            try:
                self.socket_pkt.recvfrom(0)
                print("PACOTE DADOS RECEBIDO")
                self.recv_data_msg()
            except:
                traceback.print_exc()
                continue
        print("SAIU DO SOCKET")

    ##########################################
    # Set timers
    ##########################################
    # Originator timers
    def set_source_active_timer(self):
        self.clear_source_active_timer()
        self._source_active_timer = Timer(SOURCE_LIFETIME, self.source_active_timeout)
        self._source_active_timer.start()

    def clear_source_active_timer(self):
        if self._source_active_timer is not None:
            self._source_active_timer.cancel()


    ###########################################
    # Timer timeout
    ###########################################
    def source_active_timeout(self):
        self._kernel_entry.sat_expires()

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        if self.is_S_directly_conn():
            self.set_source_active_timer()
            if self.is_tree_inactive():
                self._kernel_entry.sat_running()


    ###########################################
    # Change to in/out-tree
    ###########################################
    def send_my_interest(self):
        return

    def node_is_out_tree(self):
        return

    def node_is_in_tree(self):
        return

    ####################################################################
    #Override
    def is_forwarding(self):
        return False

    #Override
    def delete(self):
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

    def is_downstream(self):
        return False
