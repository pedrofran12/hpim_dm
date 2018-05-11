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
from .root_reliable import SFMRUpstreamStates
import traceback
from . import DataPacketsSocket
import threading
import logging
import Main


class TreeInterfaceUpstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, best_upstream_router, was_non_root=False):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceUpstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, logger)

        # Reliable State
        #from .root_reliable import SFMRRootState
        #self._reliable_state = SFMRRootState
        #self._reliable_state_timer = None
        #self._install_timer = None

        # todo e preciso o was_in_tree???
        self._was_in_tree = False
        self._block_timer = None
        self._interest_timer = None
        self._msg_being_reliably_sent = None
        self._neighbors_that_acked = set()
        if was_non_root:
            self._upstream_state = SFMRUpstreamStates.BLOCKED
            self._upstream_state.non_root_interface_to_root_interface(self)
        else:
            self._upstream_state = SFMRUpstreamStates.UNBLOCKED
            #self.send_my_interest()




        #self._assert_winner_metric = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        #self.assert_logger.debug(str(self._assert_state))

        # Originator state
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

    def set_upstream_state(self, new_state):
        if new_state != self._upstream_state:
            self._upstream_state = new_state
        #new_state.transition(self)
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
    def set_block_timer(self):
        self.clear_block_timer()
        self._block_timer = Timer(10, self.block_timeout)
        self._block_timer.start()

    def clear_block_timer(self):
        if self._block_timer is not None:
            self._block_timer.cancel()

    def set_interest_timer(self):
        self.clear_interest_timer()
        self._interest_timer = Timer(10, self.interest_timeout)
        self._interest_timer.start()

    def clear_interest_timer(self):
        if self._interest_timer is not None:
            self._interest_timer.cancel()

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
    def block_timeout(self):
        self._upstream_state.block_timer_expires(self)

    def interest_timeout(self):
        self._upstream_state.interest_timer_expires(self)

    def source_active_timeout(self):
        if self.is_S_directly_conn():
            #self._kernel_entry.delete(flood_remove_tree=True)
            #self._kernel_entry.transition_to_inactive()
            self._kernel_entry.change_tree_to_unknown_state()

    ###########################################
    # Neighbors that acked
    ###########################################
    def clear_neighbors_that_acked_list(self):
        # todo lock
        self._neighbors_that_acked = {}

    def check_if_all_neighbors_acked(self, neighbor_ip):
        self._neighbors_that_acked.add(neighbor_ip)

        if self.get_interface().did_all_neighbors_acked(self._neighbors_that_acked):
            if not self.is_tree_active():
                self._kernel_entry.notify
            if self._best_upstream_router is not None:
                # verificar se existe aw
                self._upstream_state.all_neighbors_acked_and_there_is_aw(self)
            else:
                # verificar se nao existe aw
                self._upstream_state.all_neighbors_acked_and_there_is_no_aw(self)

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        if self.is_S_directly_conn():
            self.set_source_active_timer()

    '''
    def recv_quack_msg(self, neighbor_ip, captured_states: dict):
        if neighbor_ip == self._assert_winner and self.get_ip() in captured_states and captured_states.get(self.get_ip()).counter == self._my_counter():
            # info correct
            self._reliable_state.receive_quack_from_aw_and_info_correct(self)
        else:
            # info incorrect or not existent
            self._reliable_state.receive_quack_from_aw_and_info_incorrect(self)
        
        if captured_states.get(self.get_ip()).state == self.get_my_interest_state_flag():
            #self._last_neighbor_that_correctly_acked = neighbor_ip
            self._reliable_state.receive_ack_and_info_correct(self)
            # todo guardar last_neighbor_ack
        else:
            # info incorrect or not existent
            #self._last_neighbor_that_correctly_acked = None
            self._reliable_state.receive_ack_and_info_incorrect_or_not_existent(self)
            # todo apagar last_neighbor_ack
        
    '''
    def change_assert_state(self, assert_state):
        best_upstream_router = self._best_upstream_router
        super().change_assert_state(assert_state)

        if assert_state is None:
            self._upstream_state.recv_uninstall_from_aw_and_there_are_no_upstream_routers(self)
            #self.transition_to_inactive()

        elif best_upstream_router is None or best_upstream_router != assert_state:
            self._upstream_state.recv_install_from_aw(self)
            #self.transition_to_active()

    def change_interest_state(self, interest_state):
        return

    '''
    def recv_install_msg(self, neighbor_ip, metric_state):
        super().recv_install_msg(neighbor_ip, metric_state)
        self.calculate_assert_winner()
        if self._assert_winner.get_ip() == neighbor_ip:
            self._upstream_state.recv_install_from_aw(self)

    def recv_uninstall_msg(self, neighbor_ip):
        last_assert_winner = self._assert_winner.get_ip() if self._assert_winner is not None else None
        #last_assert_winner = self._assert_winner.get_ip()
        super().recv_uninstall_msg(neighbor_ip)
        self.calculate_assert_winner()

        current_assert_winner = self._assert_winner
        if last_assert_winner == neighbor_ip and current_assert_winner is not None:
            self._upstream_state.recv_uninstall_from_aw_and_there_are_upstream_routers(self)
        else:
            self._upstream_state.recv_uninstall_from_aw_and_there_are_no_upstream_routers(self)
    '''

    def recv_ack_msg(self, neighbor_ip, sn):
        if self._msg_being_reliably_sent is not None and sn == self._msg_being_reliably_sent[0].payload.payload.sequence_number:
            self._upstream_state.neighbor_acks_and_sn_is_fresh(self, neighbor_ip)

    ############################################
    #
    ############################################
    def transition_to_active(self):
        self.send_my_interest()

    def transition_to_inactive(self):
        # todo verificar melhor por causa do estado blocked
        if self._upstream_state == SFMRUpstreamStates.UNBLOCKED:
            self._kernel_entry.notify_interface_is_ready_to_remove(self._interface_id)



    ###########################################
    # Change to in/out-tree
    ###########################################
    def send_my_interest(self):
        if self.is_node_in_tree() and not self.is_S_directly_conn():
            self.node_is_in_tree(force=True)
        elif not self.is_S_directly_conn():
            self.node_is_out_tree(force=True)


    def node_is_out_tree(self, force=False):
        # TODO LOCK PARA COUNTER E ESTADO
        #if not self.is_S_directly_conn() and (self._was_in_tree or force) and self._best_upstream_router is not None:
        if self.is_tree_active() and not self.is_S_directly_conn() and self._best_upstream_router is not None:
            self._upstream_state.transition_to_ot(self)
            self._was_in_tree = False

    def node_is_in_tree(self, force=False):
        # TODO LOCK PARA COUNTER E ESTADO
        #if not self.is_S_directly_conn() and (not self._was_in_tree or force) and self._best_upstream_router is not None:
        if self.is_tree_active() and not self.is_S_directly_conn() and self._best_upstream_router is not None:
            self._upstream_state.transition_to_it(self)
            self._was_in_tree = True

    ###########################################
    # Change AssertWinner
    ###########################################
    def notify_assert_winner_change(self):
        self._reliable_state.aw_change(self)

    ###########################################
    # Send packets
    ###########################################
    '''
    def send_interest(self):
        print("send join_tree")
        # TODO CONCORRENCIA COUNTER
        counter = self._reliable_state_counter
        try:
            (source, group) = self.get_tree_id()
            ph = PacketProtocolJoinTree(source, group, counter)
            pckt = Packet(payload=PacketProtocolHeader(ph))
            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return

    def send_no_interest(self):
        print("send prune_tree")
        # TODO CONCORRENCIA COUNTER
        counter = self._reliable_state_counter
        try:
            (source, group) = self.get_tree_id()

            ph = PacketProtocolPruneTree(source, group, counter)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return
    '''
    def resend_last_reliable_packet(self):
        try:
            (pkt, dst) = self._msg_being_reliably_sent
            self.get_interface().send(pkt, dst)
        except:
            traceback.print_exc()

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

        self.clear_interest_timer()
        self.clear_block_timer()
        # Clear Originator state
        #self._originator_state = None

    def is_downstream(self):
        return False

    '''
    def is_originator(self):
        return self._originator_state == OriginatorState.Originator
    '''