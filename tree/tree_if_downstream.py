'''
Created on Jul 16, 2015

@author: alex
'''
from threading import Timer
from CustomTimer.RemainingTimer import RemainingTimer
from .assert_ import AssertState, SFMRAssertABC, SFMRAssertWinner
from .downstream_state import SFMRPruneState, SFMRDownstreamStateABC
from .tree_interface import TreeInterface
from Packet.PacketProtocolRemoveTree import PacketProtocolRemoveTree
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
import traceback
from .metric import AssertMetric, Metric
import logging
import Main

class TreeInterfaceDownstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.NonRootInterface')

    def __init__(self, kernel_entry, interface_id, rpc: Metric):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceDownstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, logger)
        self.assert_logger = logging.LoggerAdapter(logger.logger.getChild('Assert'), logger.extra)
        self.downstream_logger = logging.LoggerAdapter(logger.logger.getChild('Downstream'), logger.extra)

        # Reliable State
        from .non_root_reliable import SFMRReliableState
        self._reliable_state = SFMRReliableState.STABLE
        self._reliable_state_timer = None
        self._reliable_state_routers_dict = {}

        # Assert Winner State
        self._assert_state = AssertState.Winner
        self._assert_winner_metric = AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        self.assert_logger.debug(str(self._assert_state))

        # Downstream Node Interest State
        self._downstream_node_interest_state = SFMRPruneState.DI
        self._downstream_interest_pending_timer = None
        self.downstream_logger.debug(str(self._downstream_node_interest_state))
        #self._downstream_node_interest_state.is_now_non_root(self)

        self.logger.debug('Created DownstreamInterface')

        from .downstream_nodes_state_entry import StateEntry
        for neighbor_ip in self.get_interface().neighbors:
            self._reliable_state_routers_dict[neighbor_ip] = StateEntry(neighbor_ip, "NI", 0)
        self._reliable_state_routers_dict[self.get_ip()] = StateEntry(self.get_ip(), "AW", 1)

        self.set_reliable_state(SFMRReliableState.UNSTABLE)
        self.set_reliable_timer()

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
    def set_assert_state(self, new_state: SFMRAssertABC):
        with self.get_state_lock():
            if new_state != self._assert_state:
                self._assert_state = new_state
                self.assert_logger.debug(str(new_state))

                self.change_tree()
                self.evaluate_in_tree()

                # TODO METER ISTO NOUTRO SITIO
                if new_state == AssertState.Winner:
                    new_state.is_now_assert_winner(self)
                else:
                    new_state.is_now_assert_loser(self)

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
    def set_downstream_node_interest_state(self, new_state: SFMRDownstreamStateABC):
        with self.get_state_lock():
            if new_state != self._downstream_node_interest_state:
                self._downstream_node_interest_state = new_state
                self.downstream_logger.debug(str(new_state))

                self.change_tree()
                self.evaluate_in_tree()

    def check_downstream_interest(self):
        it = False
        for state in self._reliable_state_routers_dict.values():
            if state.state == "J" or state.state == "NI":
                it = True
                break

        if it:
            self._downstream_node_interest_state.in_tree(self)
        else:
            self._downstream_node_interest_state.out_tree(self)

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
    def set_reliable_timer(self):
        self.clear_reliable_timer()
        self._reliable_state_timer = Timer(10, self.reliable_timeout)
        self._reliable_state_timer.start()

    def clear_reliable_timer(self):
        if self._reliable_state_timer is not None:
            self._reliable_state_timer.cancel()

    ###########################################
    # Timer timeout
    ###########################################
    def reliable_timeout(self):
        self._reliable_state.timer_expires(self)

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        self._assert_state.data_arrival(self)

    def recv_assert_msg(self, received_metric: AssertMetric):
        if received_metric.is_better_than(self._assert_winner_metric):
            self._assert_state.recv_better_metric(self, received_metric)
        elif self._assert_winner_metric.is_better_than(received_metric):
            self._assert_state.recv_worse_metric(self, received_metric)

    # Override
    def recv_join_msg(self, join_state):
        neighbor_ip = join_state.neighbor_ip
        if neighbor_ip in self._reliable_state_routers_dict and join_state.is_better_than(self._reliable_state_routers_dict[neighbor_ip]):
            self._reliable_state_routers_dict[neighbor_ip] = join_state
            # todo check in tree

        self._reliable_state.receive_RECENT_join_prune_prunel(self)
        self.check_downstream_interest()

    def recv_prune_msg(self, prune_state):
        neighbor_ip = prune_state.neighbor_ip
        if neighbor_ip in self._reliable_state_routers_dict and prune_state.is_better_than(self._reliable_state_routers_dict[neighbor_ip]):
            self._reliable_state_routers_dict[neighbor_ip] = prune_state
            # todo check in tree

        self._reliable_state.receive_RECENT_join_prune_prunel(self)
        self.check_downstream_interest()


    def recv_prune_l_msg(self, states):
        for neighbor_ip, state in states.items():
            if neighbor_ip in self._reliable_state_routers_dict and state.is_better_than(self._reliable_state_routers_dict[neighbor_ip]):
                self._reliable_state_routers_dict[neighbor_ip] = state
                # todo check in tree

        self._reliable_state.receive_RECENT_join_prune_prunel(self)
        self.check_downstream_interest()


    def recv_quack_msg(self, neighbor_ip, states):
        for neighbor_ip, state in states.items():
            if neighbor_ip in self._reliable_state_routers_dict and state.is_better_than(self._reliable_state_routers_dict[neighbor_ip]):
                self._reliable_state_routers_dict[neighbor_ip] = state

        if self._assert_state == AssertState.Winner:
            #If im AW there is at least other router thinking that it is AW
            self._reliable_state.receive_ack_and_info_incorrect_or_not_existent(self)
        elif self.get_ip() in states and states[self.get_ip()].state == 'AL':
            # Im AL and want to check if AW received my info correctly
            self._reliable_state.receive_ack_and_info_correct(self)
        else:
            # Im AL and AW didnt receive my info correctly
            self._reliable_state.receive_ack_and_info_incorrect_or_not_existent(self)

        self.check_downstream_interest()


    '''
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
    def send_remove_tree(self):
        print("send remove tree")

        try:
            (source, group) = self.get_tree_id()
            ph = PacketProtocolRemoveTree(source, group)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            self.get_interface().send_reliably(pckt)
        except:
            traceback.print_exc()
            return

    def send_quack(self):
        from Packet.PacketProtocolTreeInterestQuery import PacketProtocolQuack
        try:
            (source, group) = self.get_tree_id()
            ph = PacketProtocolQuack(source, group, self._reliable_state_routers_dict)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            self.get_interface().send(pckt)
            #self.get_interface().send_reliably(pckt)
        except:
            traceback.print_exc()
            return

    def send_prune_l(self):
        from Packet.PacketProtocolTreeInterestQuery import PacketProtocolPruneL
        try:
            (source, group) = self.get_tree_id()
            ph = PacketProtocolPruneL(source, group, self._reliable_state_routers_dict)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            self.get_interface().send(pckt)
            #self.get_interface().send_reliably(pckt)
        except:
            traceback.print_exc()
            return

    ##########################################################

    # Override
    def is_forwarding(self):
        return self.is_in_tree() and self.is_assert_winner()

    def is_in_tree(self):
        return self.igmp_has_members() or self.are_downstream_nodes_interested()

    def are_downstream_nodes_interested(self):
        to_forward = False
        for neighbor_state in self._reliable_state_routers_dict.values():
            if neighbor_state.state == "J" or neighbor_state.state == "NI":
                to_forward = True
                break
        return (self._downstream_node_interest_state == SFMRPruneState.DI) or to_forward


    # Override
    def neighbor_removal(self, other_neighbors_remain):
        if other_neighbors_remain:
            self._downstream_node_interest_state.lost_nbr(self)
        else:
            self._downstream_node_interest_state.lost_last_nbr(self)

    # Override
    def delete(self, change_type_interface=False):
        super().delete(change_type_interface)

        # Downstream state
        #self.clear_downstream_interest_pending_timer()
        #self._downstream_node_interest_state = None

        # Assert State
        if change_type_interface:
            self._assert_state.is_now_root(self)

        self._assert_state = None
        self.set_assert_winner_metric(AssertMetric.infinite_assert_metric())  # unsubscribe from current AssertWinner NeighborLivenessTimer
        self._assert_winner_metric = None


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
