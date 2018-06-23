from threading import Timer
from CustomTimer.RemainingTimer import RemainingTimer
from .assert_state import AssertState, SFMRAssertABC, SFMRAssertWinner
from .downstream_state import SFMRPruneState, SFMRDownstreamStateABC
from .tree_interface import TreeInterface
from Packet.PacketProtocolRemoveTree import PacketProtocolUninstallTree
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
from .non_root_state_machine import SFMRNonRootState, SFMRNonRootStateABC

import traceback
from .metric import AssertMetric, Metric
import logging
import Main

class TreeInterfaceDownstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.NonRootInterface')

    def __init__(self, kernel_entry, interface_id, rpc: Metric, best_upstream_router=None, interest_state=True, tree_is_active=False, was_root=False):
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

        #from .reliability import MessageReliabilityStates
        #self._message_state = MessageReliabilityStates.UPSTREAM
        self._downstream_state = SFMRNonRootState.UPSTREAM
        # todo saber activo ou inativo


        #self._retransmission_timer = None
        #self._msg_being_reliably_sent = None
        #self._neighbors_that_acked = set()
        #self._neighbors_interest = {}
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

        if tree_is_active:
            self._downstream_state.root_interface_to_non_root_or_new_tree_or_transition_to_active(self)
        else:
            self._downstream_state.tree_transitions_to_inactive_or_unknown(self)
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
    # Set Message state
    ############################################
    def set_message_state(self, new_state):
        if new_state != self._message_state:
            self._message_state = new_state

            #self.originator_logger.debug(str(new_state))



    ############################################
    # Set ASSERT State
    ############################################
    def calculate_assert_winner(self):
        print("CALCULATE ASSERT WINNER")
        if self._best_upstream_router is None:
            print("BEST_UPSTREAM IS NONE")
            self.set_assert_state(AssertState.Winner)
        elif self._my_assert_rpc.is_better_than(self._best_upstream_router):
            print("GANHOU ASSERT!!!!!!")
            print("EU GANHEI A: ", self._best_upstream_router.metric_preference, self._best_upstream_router.route_metric,  self._best_upstream_router.get_ip())
            print("ME: ", self._my_assert_rpc.metric_preference, self._my_assert_rpc.route_metric,  self._my_assert_rpc.get_ip())
            self.set_assert_state(AssertState.Winner)
        else:
            print("PERDEU ASSERT!!!!!!")
            print("EU PERDI A: ", self._best_upstream_router.metric_preference, self._best_upstream_router.route_metric,  self._best_upstream_router.get_ip())
            print("ME: ", self._my_assert_rpc.metric_preference, self._my_assert_rpc.route_metric,  self._my_assert_rpc.get_ip())
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
    # Set NonRoot state
    ##########################################
    def set_non_root_interface_state(self, new_state: SFMRNonRootStateABC):
        with self.get_state_lock():
            if new_state != self._downstream_node_interest_state:
                self._downstream_state = new_state
                self.downstream_logger.debug(str(new_state))

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
    def tree_transition_to_active(self):
        if self._downstream_state != SFMRNonRootState.UPSTREAM:
            self._downstream_state.root_interface_to_non_root_or_new_tree_or_transition_to_active(self)

    def tree_transition_to_inactive_or_unknown(self):
        if self._downstream_state == SFMRNonRootState.UPSTREAM:
            self._downstream_state.tree_transitions_to_inactive_or_unknown(self)



    ##########################################
    # Set timers
    ##########################################
    # Reliable timer
    '''
    def set_retransmission_timer(self):
        self.clear_retransmission_timer()
        self._retransmission_timer = Timer(10, self.retransmission_timeout)
        self._retransmission_timer.start()

    def clear_retransmission_timer(self):
        if self._retransmission_timer is not None:
            self._retransmission_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def retransmission_timeout(self):
        self._message_state.retransmission_timer_expires(self)
    '''
    ###########################################
    # Neighbors state
    ###########################################
    '''
    def clear_neighbors_that_acked_list(self):
        # todo lock
        self._neighbors_that_acked = set()

    def neighbor_acked(self, neighbor_ip):
        self._neighbors_that_acked.add(neighbor_ip)
        self.check_if_all_neighbors_acked()

    def check_if_all_neighbors_acked(self):
        if self.did_all_neighbors_acked():
            self._message_state.all_neighbors_acked(self)

    def did_all_neighbors_acked(self):
        return self._msg_being_reliably_sent is None or \
               self.get_interface().did_all_neighbors_acked(self._neighbors_that_acked)

    def message_has_been_reliable_transmitted(self):
        self._downstream_state.message_has_been_reliably_transmitted(self)
    '''

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        return
        #self._assert_state.data_arrival(self)

    def change_assert_state(self, assert_state):
        best_upstream_router = self._best_upstream_router
        super().change_assert_state(assert_state)
        self.calculate_assert_winner()

        if best_upstream_router is None and assert_state is not None or \
                best_upstream_router is not None and assert_state is None or \
                best_upstream_router is not assert_state:
            self._downstream_state.tree_is_inactive_and_best_upstream_router_reelected(self)


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

    '''
    def recv_ack_msg(self, neighbor_ip, sn):
        msg = None
        dst = None
        if self._msg_being_reliably_sent is not None:
            (msg, dst) = self._msg_being_reliably_sent

        if msg is not None and dst is None and sn == msg.payload.payload.sequence_number or \
                msg is not None and dst == neighbor_ip and sn == msg.payload.payload.sequence_number:
            #self._downstream_state.receive_ack_from_neighbor_and_sn_fresh(self, neighbor_ip)
            self._message_state.receive_ack_and_sn_is_fresh(self, neighbor_ip)

    def recv_ack_sync_msg(self, neighbor_ip, minimum_sn):
        msg = None
        if self._msg_being_reliably_sent is not None:
            (msg, _) = self._msg_being_reliably_sent

        if msg is not None and msg.payload.payload.sequence_number < minimum_sn:
            self._message_state.receive_ack_and_sn_is_fresh(self, neighbor_ip)
            #self._downstream_state.receive_ack_from_neighbor_and_sn_fresh(self, neighbor_ip)

    '''
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
    def send_i_am_upstream(self):
        #self._message_state.send_new_i_am_upstream(self, self._my_assert_rpc)
        (source, group) = self.get_tree_id()
        self.get_interface().send_i_am_upstream(source, group, self._my_assert_rpc)

    def send_i_am_no_longer_upstream(self):
        #self._message_state.send_new_i_am_no_longer_upstream(self)
        (source, group) = self.get_tree_id()
        self.get_interface().send_i_am_no_longer_upstream(source, group)

    def send_interest(self):
        #self._message_state.send_new_interest(self)
        (source, group) = self.get_tree_id()
        best_upstream_neighbor = self._best_upstream_router.get_ip()
        self.get_interface().send_interest(source, group, best_upstream_neighbor)

    def send_no_interest(self):
        #self._message_state.send_new_no_interest(self)
        (source, group) = self.get_tree_id()
        best_upstream_neighbor = self._best_upstream_router.get_ip()
        self.get_interface().send_no_interest(source, group, best_upstream_neighbor)

    def cancel_message(self):
        #self._message_state.cancel_message(self)
        #self.get_interface().cancel_message(self.get_tree_id())
        self.get_interface().cancel_interest_message(self.get_tree_id())

    '''
    def resend_last_reliable_packet(self):
        if self._msg_being_reliably_sent is None:
            return
        (msg, dst) = self._msg_being_reliably_sent
        try:
            if msg is not None and dst is None:
                self.get_interface().send(msg)
            elif msg is not None:
                self.get_interface().send(msg, dst)
        except:
            traceback.print_exc()
    '''

    def get_sync_state(self):
        if self._downstream_state == SFMRNonRootState.UPSTREAM:
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
    '''
    def neighbor_removal(self, other_neighbors_remain):
        if other_neighbors_remain:
            self._downstream_node_interest_state.lost_nbr(self)
        else:
            self._downstream_node_interest_state.lost_last_nbr(self)
    '''

    # Override
    def delete(self):
        super().delete()

        self.cancel_message()
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
        self._downstream_state.my_rpc_changes(self)
        self.calculate_assert_winner()
