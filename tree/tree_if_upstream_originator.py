'''
Created on Jul 16, 2015

@author: alex
'''
from .tree_interface import TreeInterface
from threading import Timer
from CustomTimer.RemainingTimer import RemainingTimer
from .globals import *
import random
from .metric import AssertMetric
#from Packet.PacketPimStateRefresh import PacketPimStateRefresh
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
from .reliability import MessageReliabilityABC
import traceback
from . import DataPacketsSocket
import threading
import logging
import Main


class TreeInterfaceUpstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, best_upstream_router):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceUpstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, logger)

        # Originator state
        self._source_active_timer = None
        if self.is_S_directly_conn():
            self.set_source_active_timer()

        # TODO TESTE SOCKET RECV DATA PCKTS
        self.socket_is_enabled = True
        (s,g) = self.get_tree_id()
        interface_name = self.get_interface().interface_name
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
                #self._kernel_entry.change_tree_to_active_state()
                self._kernel_entry.sat_running()

    '''
    def recv_ack_msg(self, neighbor_ip, sn):
        return

    def recv_ack_sync_msg(self, neighbor_ip, minimum_sn):
        return
    '''

    ############################################
    #
    ############################################
    def tree_transition_to_active(self):
        return

    def tree_transition_to_inactive_or_unknown(self):
        return


    ###########################################
    # Change to in/out-tree
    ###########################################
    def send_my_interest(self):
        return

    def node_is_out_tree(self, force=False):
        return

    def node_is_in_tree(self, force=False):
        return

    ###########################################
    # Change AssertWinner
    ###########################################
    '''
    def notify_assert_winner_change(self):
        self._reliable_state.aw_change(self)
    '''

    ###########################################
    # Changes to RPF'(s)
    ###########################################
    # caused by unicast routing table:
    '''
    def change_on_unicast_routing(self, interface_change=False):
        self.change_rpf(self.is_node_in_tree(), interface_change)
    
        if self.is_S_directly_conn():
            self._graft_prune_state.sourceIsNowDirectConnect(self)
        else:
            self._originator_state.SourceNotConnected(self)
    '''

    ####################################################################
    #Override
    def is_forwarding(self):
        return False

    # If new/reset neighbor is RPF neighbor => clear prune limit timer
    '''
    def new_or_reset_neighbor(self, neighbor_ip):
        if neighbor_ip == self.get_neighbor_RPF():
            self.clear_prune_limit_timer()
    '''
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

    '''
    def is_originator(self):
        return self._originator_state == OriginatorState.Originator
    '''
