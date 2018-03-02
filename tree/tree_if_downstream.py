'''
Created on Jul 16, 2015

@author: alex
'''
from threading import Timer
from CustomTimer.RemainingTimer import RemainingTimer
from .assert_ import AssertState, SFMRAssertABC, SFMRAssertWinner
from .prune import SFMRPruneState, SFMRPruneStateABC, SFMRDownstreamInterested, SFMRDownstreamInterestedPending
from .tree_interface import TreeInterface
from Packet.PacketPimStateRefresh import PacketPimStateRefresh
from Packet.Packet import Packet
from Packet.PacketPimHeader import PacketPimHeader
import traceback
from .metric import AssertMetric, Metric
import logging
import Main

class TreeInterfaceDownstream(TreeInterface):
    LOGGER = logging.getLogger('pim.KernelEntry.DownstreamInterface')

    def __init__(self, kernel_entry, interface_id, rpc: Metric):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceDownstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, logger)

        # Assert Winner State
        self._assert_state = AssertState.Winner
        self._assert_winner_metric = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        self.assert_logger.debug("LOGGER ASSERT ... msg")

        # Downstream Node Interest State
        self._downstream_node_interest_state = SFMRPruneState.DIP
        self._downstream_interest_pending_timer = None
        self.join_prune_logger.debug(str(self._downstream_node_interest_state))
        self._downstream_node_interest_state.is_now_non_root(self)

        self.logger.debug('Created DownstreamInterface')

    ############################################
    # Set ASSERT State
    ############################################
    def set_assert_state(self, new_state: SFMRAssertABC):
        with self.get_state_lock():
            if new_state != self._assert_state:
                self._assert_state = new_state
                self.assert_logger.debug(str(new_state))

                self.change_tree()
                self.evaluate_ingroup()

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

    ##########################################
    # Set Downstream Node Interest state
    ##########################################
    def set_downstream_node_interest_state(self, new_state: SFMRPruneStateABC):
        with self.get_state_lock():
            if new_state != self._downstream_node_interest_state:
                self._downstream_node_interest_state = new_state
                self.join_prune_logger.debug(str(new_state))

                self.change_tree()
                self.evaluate_ingroup()

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
    def set_downstream_interest_pending_timer(self, time=5):
        self.clear_downstream_interest_pending_timer()
        self._downstream_interest_pending_timer = Timer(time, self.downstream_interest_pending_timeout)
        self._downstream_interest_pending_timer.start()

    def clear_downstream_interest_pending_timer(self):
        if self._downstream_interest_pending_timer is not None:
            self._downstream_interest_pending_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def downstream_interest_pending_timeout(self):
        self._downstream_node_interest_state.dipt_expires(self)

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        self._assert_state.data_arrival(self)

    def recv_assert_msg(self, received_metric: AssertMetric):
        if received_metric.is_better_than(self._assert_winner_metric):
            self._assert_state.recv_better_metric(self, received_metric)
        else:
            self._assert_state.recv_worse_metric(self, received_metric)
        # TODO falta considerar protected assert

    # Override
    '''
    def recv_prune_msg(self, upstream_neighbor_address, holdtime):
        # todo
        return
    '''

    # Override
    def recv_join_msg(self):
        self._downstream_node_interest_state.recv_join(self)

    # Override
    def recv_tree_interest_query_msg(self):
        number_of_neighbors = self.number_of_neighbors()
        if number_of_neighbors == 1:
            self._downstream_node_interest_state.recv_tree_interest_query_1nbr(self)
        elif number_of_neighbors > 1:
            self._downstream_node_interest_state.recv_tree_interest_query(self)


    ##########################################################

    # Override
    def is_forwarding(self):
        return self.is_in_tree() and self.is_assert_winner()

    def is_in_tree(self):
        return self.igmp_has_members() or self.are_downstream_nodes_interested()

    def are_downstream_nodes_interested(self):
        return (self._downstream_node_interest_state == SFMRPruneState.DIP) or (self._downstream_node_interest_state == SFMRPruneState.DI)


    # Override
    # When new neighbor connects, send last state refresh msg
    def neighbor_removal(self, other_neighbors_remain):
        if other_neighbors_remain:
            self._downstream_node_interest_state.lost_nbr(self)
        else:
            self._downstream_node_interest_state.lost_last_nbr(self)

    # Override
    def delete(self, change_type_interface=False):
        super().delete(change_type_interface)
        self.clear_downstream_interest_pending_timer()

    def is_downstream(self):
        return True

    def is_assert_winner(self):
        return self._assert_state == AssertState.Winner

    def assert_winner_nlt_expires(self):
        self._assert_state.aw_failure(self)


    def notify_rpc_change(self, new_rpc: Metric):
        if new_rpc == self._assert_winner_metric:
            return

        my_new_assert_metric = AssertMetric(new_rpc.metric_preference, new_rpc.route_metric, self.get_ip())
        if my_new_assert_metric.is_better_than(self._assert_winner_metric):
            self._assert_state.my_rpc_is_better_than_aw(self, my_new_assert_metric)
        else:
            self._assert_state.my_rpc_is_worse_than_aw(self, my_new_assert_metric)
