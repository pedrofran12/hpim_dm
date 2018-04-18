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
from Packet.PacketProtocolJoinTree import PacketProtocolJoinTree, PacketProtocolPruneTree
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
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

        # Reliable State
        from .root_reliable import SFMRReliableState
        self._reliable_state = SFMRReliableState.STABLE
        self._reliable_state_timer = None
        self._last_neighbor_that_correctly_acked = None
        self._reliable_state_counter = 0

        #self._assert_winner_metric = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        #self.assert_logger.debug(str(self._assert_state))

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
    # Get IT/OT state flag
    ##########################################
    def get_my_interest_state_flag(self):
        if self.is_node_in_tree():
            return "J"
        else:
            return "P"

    ##########################################
    # Set state
    ##########################################
    '''
    def set_originator_state(self, new_state):
        if new_state != self._originator_state:
            self._originator_state = new_state
            self.originator_logger.debug(str(new_state))
    '''

    def set_reliable_state(self, new_state):
        if new_state != self._reliable_state:
            self._reliable_state = new_state
        new_state.transition(self)
            #self.originator_logger.debug(str(new_state))

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
    # Reliable timer
    def set_reliable_timer(self):
        self.clear_reliable_timer()
        self._reliable_state_timer = Timer(10, self.reliable_timeout)
        self._reliable_state_timer.start()

    def clear_reliable_timer(self):
        if self._reliable_state_timer is not None:
            self._reliable_state_timer.cancel()


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
    def reliable_timeout(self):
        self._reliable_state.timer_expires(self)

    def source_active_timeout(self):
        if self.is_S_directly_conn():
            self._kernel_entry.delete(flood_remove_tree=True)

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        if self.is_S_directly_conn():
            self.set_source_active_timer()

    def recv_quack_msg(self, neighbor_ip, captured_states: dict):
        if captured_states.get(self.get_ip()).state == self.get_my_interest_state_flag():
            # info correct
            self._last_neighbor_that_correctly_acked = neighbor_ip
            self._reliable_state.receive_ack_and_info_correct(self)
            # todo guardar last_neighbor_ack
        else:
            # info incorrect or not existent
            self._last_neighbor_that_correctly_acked = None
            self._reliable_state.receive_ack_and_info_incorrect_or_not_existent(self)
            # todo apagar last_neighbor_ack

    ###########################################
    # Change to in/out-tree
    ###########################################
    def node_is_out_tree(self):
        # TODO LOCK PARA COUNTER E ESTADO
        from .root_reliable import SFMRReliableState
        self.set_reliable_state(SFMRReliableState.UNSTABLE)
        self.send_prune_tree()

    def node_is_in_tree(self):
        # TODO LOCK PARA COUNTER E ESTADO
        from .root_reliable import SFMRReliableState
        self.set_reliable_state(SFMRReliableState.UNSTABLE)
        self.send_join_tree()


    ###########################################
    # Send packets
    ###########################################
    def send_join_tree(self):
        print("send join_tree")
        # TODO CONCORRENCIA COUNTER
        self._reliable_state_counter += 1
        counter = self._reliable_state_counter
        try:
            (source, group) = self.get_tree_id()
            ph = PacketProtocolJoinTree(source, group, counter)
            pckt = Packet(payload=PacketProtocolHeader(ph))
            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return

    def send_prune_tree(self):
        print("send prune_tree")
        # TODO CONCORRENCIA COUNTER
        self._reliable_state_counter += 1
        counter = self._reliable_state_counter
        try:
            (source, group) = self.get_tree_id()

            ph = PacketProtocolPruneTree(source, group, counter)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return


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
