'''
Created on Jul 16, 2015

@author: alex
'''
from threading import Timer
from CustomTimer.RemainingTimer import RemainingTimer
from .assert_state import AssertState, SFMRAssertABC, SFMRAssertWinner
from .downstream_state import SFMRPruneState, SFMRDownstreamStateABC
from .tree_interface import TreeInterface
from Packet.PacketProtocolRemoveTree import PacketProtocolUninstallTree
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
from .non_root_reliable import SFMRNonRootState

import traceback
from .metric import AssertMetric, Metric
import logging
import Main

class TreeInterfaceDownstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.NonRootInterface')

    def __init__(self, kernel_entry, interface_id, rpc: Metric, best_upstream_router=None, interest_state=False, tree_is_active=False):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceDownstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, logger)
        self.assert_logger = logging.LoggerAdapter(logger.logger.getChild('Assert'), logger.extra)
        self.downstream_logger = logging.LoggerAdapter(logger.logger.getChild('Downstream'), logger.extra)

        # Reliable State
        #from .non_root_reliable import SFMRReliableState
        #self._reliable_state = None
        #self._reliable_state_timer = None
        #self._downstream_routers_state_dict = {}

        if tree_is_active:
            self._downstream_state = SFMRNonRootState.ACTIVE
        else:
            self._downstream_state = SFMRNonRootState.INACTIVE
        # todo saber activo ou inativo


        self._install_timer = None
        self._msg_being_reliably_sent = None
        self._neighbors_that_acked = set()
        self._neighbors_interest = {}
        #self._neighbors_upstream = {}  # todo talvez ja esteja na interface upstream

        # Downstream Node Interest State
        if interest_state:
            self._downstream_node_interest_state = SFMRPruneState.DI
        else:
            self._downstream_node_interest_state = SFMRPruneState.NDI
        #self._downstream_interest_pending_timer = None
        #self.downstream_logger.debug(str(self._downstream_node_interest_state))
        #self._downstream_node_interest_state.is_now_non_root(self)

        # Assert Winner State
        self._assert_state = AssertState.Winner
        self._my_assert_rpc = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        # self._assert_winner_metric = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        #self._upstream_routers[self.get_ip()] = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        self.calculate_assert_winner()
        # self.assert_logger.debug(str(self._assert_state))

        self.logger.debug('Created DownstreamInterface')


        self._downstream_state.root_interface_to_non_root_or_new_tree_or_transition_to_active(self)
        '''
        from .downstream_nodes_state_entry import DownstreamStateEntry
        for neighbor_ip in self.get_interface().neighbors:
            if neighbor_ip not in self._upstream_routers:
                self._downstream_routers_state_dict[neighbor_ip] = DownstreamStateEntry(neighbor_ip, "NI", 0)
        '''
        '''
        if self.calculate_assert_winner().ip == self.get_ip():
            self._reliable_state = SFMRReliableState.AW
            self._reliable_state.transition_to_assert_winner(self)
        else:
            self._reliable_state = SFMRReliableState.AL
            self._reliable_state.transition_to_assert_loser(self)
        '''
        #self.set_reliable_state(SFMRReliableState.UNSTABLE)
        #self.set_reliable_timer()

    ############################################
    # Set Reliable state
    ############################################
    def set_reliable_state(self, new_state, reset_timer = False):
        if new_state != self._reliable_state:
            self._reliable_state = new_state
            new_state.transition(self)
        elif reset_timer:
            new_state.transition(self)

            #self.originator_logger.debug(str(new_state))


    ############################################
    # Set ASSERT State
    ############################################
    def calculate_assert_winner(self):
        if self._best_upstream_router is None:
            self.set_assert_state(AssertState.Winner)
        elif self._my_assert_rpc.is_better_than(self._best_upstream_router):
            self.set_assert_state(AssertState.Winner)
        else:
            self.set_assert_state(AssertState.Loser)

    def set_assert_state(self, new_state: SFMRAssertABC):
        with self.get_state_lock():
            if new_state != self._assert_state:
                self._assert_state = new_state
                self.assert_logger.debug(str(new_state))

                self.change_tree()
                self.evaluate_in_tree()

    '''
    def set_assert_winner_metric(self, new_assert_metric: AssertMetric):
        with self.get_state_lock():
            try:
                old_neighbor = self.get_interface().get_neighbor(self._assert_winner_metric.get_ip())
                new_neighbor = self.get_interface().get_neighbor(new_assert_metric.get_ip())

                if old_neighbor is not None:
                    old_neighbor.unsubscribe_nlt_expiration(self)
                if new_neighbor is not None:
                    new_neighbor.subscribe_nlt_expiration(self)
            except:
                traceback.print_exc()
            finally:
                self._assert_winner_metric = new_assert_metric
    '''

    ##########################################
    # Set Downstream Node Interest state
    ##########################################
    def set_downstream_node_interest_state(self, new_state: SFMRDownstreamStateABC):
        with self.get_state_lock():
            if new_state != self._downstream_node_interest_state:
                self._downstream_node_interest_state = new_state
                self.downstream_logger.debug(str(new_state))

                self.change_tree()
                self.evaluate_in_tree()
    '''
    def check_downstream_interest(self):
        tree = self.get_tree_id()
        if self.get_interface().are_neighbors_interested(tree):
            self._downstream_node_interest_state.in_tree(self)
        else:
            self._downstream_node_interest_state.out_tree(self)
    '''


    ############################################
    #
    ############################################
    def transition_to_active(self):
        if self._downstream_state != SFMRNonRootState.ACTIVE:
            self._downstream_state = SFMRNonRootState.ACTIVE
            self._downstream_state.root_interface_to_non_root_or_new_tree_or_transition_to_active(self)

    def transition_to_inactive(self):
        if self._downstream_state != SFMRNonRootState.INACTIVE:
            self._downstream_state = SFMRNonRootState.INACTIVE
            self._downstream_state.tree_transitions_to_inactive(self)



    ##########################################
    # Check timers
    ##########################################
    '''
    def is_prune_pending_timer_running(self):
        return self._prune_pending_timer is not None and self._prune_pending_timer.is_alive()

    def is_prune_timer_running(self):
        return self._prune_timer is not None and self._prune_timer.is_alive()

    def remaining_prune_timer(self):
        return 0 if not self._prune_timer else self._prune_timer.time_remaining()
    '''
    ##########################################
    # Set timers
    ##########################################
    # Reliable timer
    def set_install_timer(self):
        self.clear_install_timer()
        self._install_timer = Timer(10, self.install_timeout)
        self._install_timer.start()

    def clear_install_timer(self):
        if self._install_timer is not None:
            self._install_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def install_timeout(self):
        self._downstream_state.install_timer_expires(self)

    ###########################################
    # Neighbors state
    ###########################################
    def clear_neighbors_that_acked_list(self):
        # todo lock
        self._neighbors_that_acked = set()

    def neighbor_acked(self, neighbor_ip):
        self._neighbors_that_acked.add(neighbor_ip)
        self.check_if_all_neighbors_acked()

    def check_if_all_neighbors_acked(self):
        if self.get_interface().did_all_neighbors_acked(self._neighbors_that_acked):
            self._downstream_state.all_neighbors_acked(self)

    '''
    def set_neighbor_interest(self, neighbor_ip, is_interested):
        self._neighbors_interest[neighbor_ip] = is_interested

        print(self._neighbors_interest.values())
        for interest in self._neighbors_interest.values():
            if interest:
                print("EXISTE INTERESSE!!!!")
                self._downstream_node_interest_state.in_tree(self)
                return

        print("NAOOOOO EXISTE INTERESSE!!!!")
        self._downstream_node_interest_state.out_tree(self)

    def set_upstream_node_state(self, neighbor_ip, state):
        self._neighbors_interest.pop(neighbor_ip)
        #self._neighbors_upstream[neighbor_ip] = state

        # todo recalcular AW


    def clear_upstream_node_state(self, neighbor_ip):
        self._neighbors_interest.pop(neighbor_ip)
        #self._neighbors_upstream.pop(neighbor_ip)

        # todo recalcular AW
    '''
    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        return
        #self._assert_state.data_arrival(self)

    '''
    def recv_assert_msg(self, received_metric: AssertMetric):
        if received_metric.is_better_than(self._assert_winner_metric):
            self._assert_state.recv_better_metric(self, received_metric)
        elif self._assert_winner_metric.is_better_than(received_metric):
            self._assert_state.recv_worse_metric(self, received_metric)
    '''

    def change_assert_state(self, assert_state):
        super().change_assert_state(assert_state)
        self.calculate_assert_winner()

    def change_interest_state(self, interest_state):
        if interest_state:
            self._downstream_node_interest_state.in_tree(self)
        else:
            self._downstream_node_interest_state.out_tree(self)


    # Override
    ''''
    def recv_interest_msg(self, neighbor_ip):
        print("RCV_INTEREST_238_TREE_IF_DOWNSTREAM")
        self._downstream_state.receive_interest_msg(self, neighbor_ip, is_interested=True)

    def recv_no_interest_msg(self, neighbor_ip):
        self._downstream_state.receive_interest_msg(self, neighbor_ip, is_interested=False)

    def recv_install_msg(self, neighbor_ip, metric_state):
        if neighbor_ip in self._neighbors_interest:
            self._neighbors_interest.pop(neighbor_ip)
        super().recv_install_msg(neighbor_ip, metric_state)
        self.calculate_assert_winner()
        #self._downstream_state.receive_install_msg(self, neighbor_ip, metric_state)

    def recv_uninstall_msg(self, neighbor_ip):
        if neighbor_ip in self._neighbors_interest:
            self._neighbors_interest.pop(neighbor_ip)
        super().recv_uninstall_msg(neighbor_ip)
        self.calculate_assert_winner()
        #self._downstream_state.receive_uninstall_msg(self, neighbor_ip)
    '''

    def recv_ack_msg(self, neighbor_ip, sn):
        if sn == self._msg_being_reliably_sent.payload.payload.sequence_number:
            self._downstream_state.receive_ack_from_neighbor_and_sn_fresh(self, neighbor_ip)

    '''
    def recv_quack_msg(self, neighbor_ip, states):
        if self.is_assert_winner():
            self._reliable_state.receive_quack_and_info_incorrect(self)
        elif neighbor_ip == self._assert_winner.ip and self.get_ip() in states:
            self._reliable_state.receive_quack_and_info_incorrect(self)

        self.check_downstream_interest()

    def recv_tree_interest_query_msg(self):
        number_of_neighbors = self.number_of_neighbors()
        if number_of_neighbors == 1:
            self._downstream_node_interest_state.recv_tree_interest_query_1nbr(self)
        elif number_of_neighbors > 1:
            self._downstream_node_interest_state.recv_tree_interest_query(self)
    '''

    ###########################################
    # Send packets
    ###########################################
    def resend_last_reliable_packet(self):
        try:
            self.get_interface().send(self._msg_being_reliably_sent)
        except:
            traceback.print_exc()

    def get_sync_state(self):
        if self._downstream_state == SFMRNonRootState.ACTIVE:
            return self._my_assert_rpc
        else:
            return None

    ##########################################################

    # Override
    def is_forwarding(self):
        return self.is_in_tree() and self.is_assert_winner()

    def is_in_tree(self):
        return self.igmp_has_members() or self.are_downstream_nodes_interested()


    def are_downstream_nodes_interested(self):
        return self._downstream_node_interest_state == SFMRPruneState.DI

    # Override
    def neighbor_removal(self, other_neighbors_remain):
        if other_neighbors_remain:
            self._downstream_node_interest_state.lost_nbr(self)
        else:
            self._downstream_node_interest_state.lost_last_nbr(self)

    # Override
    def delete(self):
        super().delete()


        self.clear_install_timer()
        # Downstream state
        #self.clear_downstream_interest_pending_timer()
        #self._downstream_node_interest_state = None

        # Assert State
        #if change_type_interface:
        #    self._assert_state.is_now_root(self)

        #self.set_assert_winner_metric(AssertMetric.infinite_assert_metric())  # unsubscribe from current AssertWinner NeighborLivenessTimer
        self._my_assert_rpc = None


    def is_downstream(self):
        return True

    def is_assert_winner(self):
        #return self._assert_state == AssertState.Winner
        return self._assert_state is not None and self._assert_state.is_assert_winner()

    def assert_winner_nlt_expires(self):
        self._assert_state.aw_failure(self)


    def notify_rpc_change(self, new_rpc: Metric):
        if new_rpc == self._my_assert_rpc:
            return

        self._my_assert_rpc = AssertMetric(new_rpc.metric_preference, new_rpc.route_metric, self.get_ip())
        #my_new_assert_metric = AssertMetric(new_rpc.metric_preference, new_rpc.route_metric, self.get_ip())
        #if my_new_assert_metric.is_better_than(self._assert_winner_metric):
        #    self._assert_state.my_rpc_is_better_than_aw(self, my_new_assert_metric)
        #else:
        #    self._assert_state.my_rpc_is_worse_than_aw(self, my_new_assert_metric)
        self._downstream_state.rpc_change(self)
        self.calculate_assert_winner()
