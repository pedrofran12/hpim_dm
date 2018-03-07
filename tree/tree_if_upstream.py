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
from Packet.PacketPimStateRefresh import PacketPimStateRefresh
import traceback
from . import DataPacketsSocket
import threading
import logging
import Main


class TreeInterfaceUpstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceUpstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, logger)

        # Originator state
        '''
        self._originator_state = OriginatorState.NotOriginator
        self._state_refresh_timer = None
        '''
        self._source_active_timer = None
        '''
        self.originator_logger = logging.LoggerAdapter(TreeInterfaceUpstream.LOGGER.getChild('Originator'), extra_dict_logger)
        self.originator_logger.debug(str(self._originator_state))
        '''

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

    ##########################################
    # Set state
    ##########################################
    '''
    def set_originator_state(self, new_state):
        if new_state != self._originator_state:
            self._originator_state = new_state
            self.originator_logger.debug(str(new_state))
    '''
    ##########################################
    # Check timers
    ##########################################
    '''

    def is_prune_limit_timer_running(self):
        return self._prune_limit_timer is not None and self._prune_limit_timer.is_alive()

    def remaining_prune_limit_timer(self):
        return 0 if not self._prune_limit_timer else self._prune_limit_timer.time_remaining()
    '''
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
        if self.is_S_directly_conn():
            self._kernel_entry.delete(flood_remove_tree=True)

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        if self.is_S_directly_conn():
            self.set_source_active_timer()

    def recv_tree_interest_query_msg(self):
        if self.is_node_in_tree():
            self.send_join_tree()

    ###########################################
    # Change to in/out-tree
    ###########################################
    def node_is_out_tree(self):
        self.send_tree_interest_query()

    def node_is_in_tree(self):
        self.send_join_tree()

    ###########################################
    # Changes to RPF'(s)
    ###########################################
    '''
    # caused by assert transition:
    def set_assert_state(self, new_state):
        super().set_assert_state(new_state)
        self.change_rpf(self.is_olist_null())
    '''
    # caused by unicast routing table:
    '''
    def change_on_unicast_routing(self, interface_change=False):
        self.change_rpf(self.is_node_in_tree(), interface_change)
    
        if self.is_S_directly_conn():
            self._graft_prune_state.sourceIsNowDirectConnect(self)
        else:
            self._originator_state.SourceNotConnected(self)
    '''

    '''
    def change_rpf(self, olist_is_null, interface_change=False):
        current_rpf = self.get_neighbor_RPF()
        if interface_change or self._last_rpf != current_rpf:
            self._last_rpf = current_rpf
            if olist_is_null:
                self._graft_prune_state.RPFnbrChanges_olistIsNull(self)
            else:
                self._graft_prune_state.RPFnbrChanges_olistIsNotNull(self)
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
    def delete(self, change_type_interface=False):
        self.socket_is_enabled = False
        self.socket_pkt.close()
        super().delete(change_type_interface)
        self.clear_source_active_timer()

        # Clear Originator state
        #self._originator_state = None

    def is_downstream(self):
        return False

    '''
    def is_originator(self):
        return self._originator_state == OriginatorState.Originator
    '''
