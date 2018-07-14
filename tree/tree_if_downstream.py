from .assert_state import AssertState, SFMRAssertABC, SFMRAssertWinner
from .downstream_state import SFMRPruneState, SFMRDownstreamStateABC
from .tree_interface import TreeInterface
from .non_root_state_machine import SFMRNonRootStateABCNEW

import traceback
from .metric import AssertMetric, Metric
import logging
import Main

class TreeInterfaceDownstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.NonRootInterface')

    def __init__(self, kernel_entry, interface_id, rpc: Metric, best_upstream_router=None, interest_state=True, was_root=False, previous_tree_state=None, current_tree_state=None):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceDownstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, logger)
        self.assert_logger = logging.LoggerAdapter(logger.logger.getChild('Assert'), logger.extra)
        self.downstream_logger = logging.LoggerAdapter(logger.logger.getChild('Downstream'), logger.extra)


        # Downstream Node Interest State
        if interest_state:
            self._downstream_node_interest_state = SFMRPruneState.DI
        else:
            self._downstream_node_interest_state = SFMRPruneState.NDI
        #self.downstream_logger.debug(str(self._downstream_node_interest_state))

        # Assert Winner State
        self._assert_state = AssertState.Winner
        self._my_assert_rpc = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        self.calculate_assert_winner()
        # self.assert_logger.debug(str(self._assert_state))

        # Deal with messages according to tree state and interface role change
        self.current_tree_state = current_tree_state
        # Event 1
        if not was_root and not previous_tree_state.is_active() and current_tree_state.is_active():
            SFMRNonRootStateABCNEW.interfaces_roles_dont_change_and_tree_transitions_to_active_state(self)
        # Event 2
        elif was_root and current_tree_state.is_active():
            SFMRNonRootStateABCNEW.interfaces_roles_change_and_tree_remains_or_transitions_to_active_state(self)
        # Event 3
        elif previous_tree_state.is_active() and current_tree_state.is_inactive() and best_upstream_router is None:
            SFMRNonRootStateABCNEW.tree_transitions_from_active_to_inactive_and_best_upstream_neighbor_is_null(self)
        # Event 4
        elif previous_tree_state.is_active() and current_tree_state.is_unknown():
            SFMRNonRootStateABCNEW.tree_transitions_from_active_to_unknown(self)
        # Event 5
        elif previous_tree_state.is_active() and current_tree_state.is_inactive() and best_upstream_router is not None:
            SFMRNonRootStateABCNEW.tree_transitions_from_active_to_inactive_and_best_upstream_neighbor_is_not_null(self)
        # Event 8
        elif previous_tree_state.is_unknown() and current_tree_state.is_inactive() and best_upstream_router is not None:
            SFMRNonRootStateABCNEW.tree_transitions_from_unknown_to_inactive_and_best_upstream_is_not_null(self)

        self.logger.debug('Created DownstreamInterface')

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

    ############################################
    # Tree transitions
    ############################################
    def tree_transition_to_active(self):
        if not self.current_tree_state.is_active():
            SFMRNonRootStateABCNEW.interfaces_roles_dont_change_and_tree_transitions_to_active_state(self)

        from .KernelEntry import ActiveTree
        self.current_tree_state = ActiveTree

    def tree_transition_to_inactive(self):
        if self.current_tree_state.is_active() and self._best_upstream_router is None:
            SFMRNonRootStateABCNEW.tree_transitions_from_active_to_inactive_and_best_upstream_neighbor_is_null(self)
        elif self.current_tree_state.is_active() and self._best_upstream_router is not None:
            SFMRNonRootStateABCNEW.tree_transitions_from_active_to_inactive_and_best_upstream_neighbor_is_not_null(self)
        elif self.current_tree_state.is_unknown() and self._best_upstream_router is not None:
            SFMRNonRootStateABCNEW.tree_transitions_from_unknown_to_inactive_and_best_upstream_is_not_null(self)

        from .KernelEntry import InactiveTree
        self.current_tree_state = InactiveTree

    def tree_transition_to_unknown(self):
        if self.current_tree_state.is_active():
            SFMRNonRootStateABCNEW.tree_transitions_from_active_to_unknown(self)

        from .KernelEntry import UnknownTree
        self.current_tree_state = UnknownTree

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

        '''
        if best_upstream_router is None and assert_state is not None or \
                best_upstream_router is not None and assert_state is None or \
                best_upstream_router is not assert_state:
            self._downstream_state.tree_is_inactive_and_best_upstream_router_reelected(self)
        '''
        # Event 6 and 7
        if self.current_tree_state.is_inactive() and assert_state is not None and \
                 (best_upstream_router is None or best_upstream_router is not assert_state):
            SFMRNonRootStateABCNEW.tree_remains_inactive_and_best_upstream_router_reelected(self)



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
        if self.get_interface() is not None:
            self.get_interface().send_i_am_upstream(source, group, self._my_assert_rpc)

    def get_sync_state(self):
        #if self._downstream_state == SFMRNonRootState.UPSTREAM:
        if self.current_tree_state.is_active():
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
    def delete(self):
        super().delete()
        #self.cancel_message()
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
        if self.current_tree_state.is_active():
            SFMRNonRootStateABCNEW.tree_is_active_and_my_rpc_changes(self)
        #self._downstream_state.my_rpc_changes(self)
        self.calculate_assert_winner()
