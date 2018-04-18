'''
Created on Jul 16, 2015

@author: alex
'''
from abc import ABCMeta, abstractmethod
import Main
from threading import RLock
import traceback

from .assert_ import AssertState, SFMRAssertABC, SFMRAssertWinner

from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.PacketProtocolJoinTree import PacketProtocolJoinTree, PacketProtocolPruneTree
#from Packet.PacketProtocolTreeInterestQuery import PacketProtocolTreeInterestQuery
from Packet.PacketProtocolAssert import PacketProtocolAssert
from Packet.Packet import Packet

from .metric import AssertMetric, Metric
from threading import Timer
from .local_membership import LocalMembership
from .globals import *
import logging

class TreeInterface(metaclass=ABCMeta):
    def __init__(self, kernel_entry, interface_id, logger: logging.LoggerAdapter):
        self._kernel_entry = kernel_entry
        self._interface_id = interface_id
        self.logger = logger

        # Local Membership State
        try:
            interface_name = Main.kernel.vif_index_to_name_dic[interface_id]
            igmp_interface = Main.igmp_interfaces[interface_name]  # type: InterfaceIGMP
            group_state = igmp_interface.interface_state.get_group_state(kernel_entry.group_ip)
            #self._igmp_has_members = group_state.add_multicast_routing_entry(self)
            igmp_has_members = group_state.add_multicast_routing_entry(self)
            self._local_membership_state = LocalMembership.Include if igmp_has_members else LocalMembership.NoInfo
        except:
            self._local_membership_state = LocalMembership.NoInfo


        # Received prune hold time
        #self._received_prune_holdtime = None

        self._igmp_lock = RLock()


    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        pass

    def recv_assert_msg(self, received_metric: AssertMetric):
        return

    def recv_join_msg(self, join_state):
        return

    def recv_prune_msg(self, prune_state):
        return

    def recv_prune_l_msg(self, states):
        return

    def recv_quack_msg(self, neighbor_ip, captured_states: dict):
        return

    #def recv_tree_interest_query_msg(self):
    #    return

    ######################################
    # Send messages
    ######################################
    '''
    def send_tree_interest_query(self):
        print("send tree_interest_query")
        try:
            (source, group) = self.get_tree_id()

            ph = PacketProtocolTreeInterestQuery(source, group)
            pckt = Packet(payload=PacketProtocolHeader(ph))
            #self.get_interface().send(pckt)
            self.get_interface().send_reliably(pckt)
        except:
            traceback.print_exc()
            return
    '''
    def send_quack(self):
        return

    def send_join_tree(self):
        print("send join_tree")
        try:
            (source, group) = self.get_tree_id()
            ph = PacketProtocolJoinTree(source, group)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            #self.get_interface().send(pckt)
            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return

    def send_prune_tree(self):
        print("send prune_tree")
        try:
            (source, group) = self.get_tree_id()

            ph = PacketProtocolPruneTree(source, group)
            pckt = Packet(payload=PacketProtocolHeader(ph))
            #self.get_interface().send(pckt)
            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return


    def send_assert(self):
        print("send assert")

        try:
            (source, group) = self.get_tree_id()
            assert_metric = self.my_rpc_metric()
            ph = PacketProtocolAssert(multicast_group_address=group, source_address=source, metric_preference=assert_metric.metric_preference, metric=assert_metric.route_metric)
            pckt = Packet(payload=PacketProtocolHeader(ph))

            self.get_interface().send(pckt)
        except:
            traceback.print_exc()
            return

    def send_protected_assert(self, infinite_metric=False):
        print("send protected assert")

        try:
            (source, group) = self.get_tree_id()
            if infinite_metric:
                import math
                ph = PacketProtocolAssert(multicast_group_address=group, source_address=source,
                                          metric_preference=math.inf, metric=math.inf)
            else:
                assert_metric = self.my_rpc_metric()
                ph = PacketProtocolAssert(multicast_group_address=group, source_address=source,
                                          metric_preference=assert_metric.metric_preference,
                                          metric=assert_metric.route_metric)

            pckt = Packet(payload=PacketProtocolHeader(ph))
            self.get_interface().send_reliably(pckt)
        except:
            traceback.print_exc()
            return

    def send_remove_tree(self):
        return

    #############################################################

    @abstractmethod
    def is_forwarding(self):
        pass

    def assert_winner_nlt_expires(self):
        return

    def neighbor_removal(self, other_neighbors_remain):
        return

    @abstractmethod
    def delete(self, change_type_interface=False):
        '''
        if change_type_interface:
            if self.could_assert():
                self._assert_state.couldAssertIsNowFalse(self)
            else:
                self._assert_state.couldAssertIsNowTrue(self)
        '''
        (s, g) = self.get_tree_id()
        # unsubscribe igmp information
        try:
            interface_name = Main.kernel.vif_index_to_name_dic[self._interface_id]
            igmp_interface = Main.igmp_interfaces[interface_name]  # type: InterfaceIGMP
            group_state = igmp_interface.interface_state.get_group_state(g)
            group_state.remove_multicast_routing_entry(self)
        except:
            pass

        print('Tree Interface deleted')

    def is_node_in_tree(self):
        return self._kernel_entry.is_in_tree()

    def evaluate_in_tree(self):
        self._kernel_entry.evaluate_in_tree_change()


    #############################################################
    # Local Membership (IGMP)
    ############################################################
    def notify_igmp(self, has_members: bool):
        with self.get_state_lock():
            with self._igmp_lock:
                if has_members != self._local_membership_state.has_members():
                    self._local_membership_state = LocalMembership.Include if has_members else LocalMembership.NoInfo
                    self.change_tree()
                    self.evaluate_in_tree()


    def igmp_has_members(self):
        with self._igmp_lock:
            return self._local_membership_state.has_members()

    def get_interface(self):
        kernel = Main.kernel
        interface_name = kernel.vif_index_to_name_dic[self._interface_id]
        interface = Main.interfaces[interface_name]
        return interface


    def get_ip(self):
        ip = self.get_interface().get_ip()
        return ip

    def number_of_neighbors(self):
        try:
            return len(self.get_interface().neighbors)
        except:
            return 0

    def get_tree_id(self):
        return (self._kernel_entry.source_ip, self._kernel_entry.group_ip)

    def change_tree(self):
        self._kernel_entry.change()

    def get_state_lock(self):
        return self._kernel_entry.CHANGE_STATE_LOCK

    @abstractmethod
    def is_downstream(self):
        raise NotImplementedError()


    '''
    # obtain ip of RPF'(S)
    def get_neighbor_RPF(self):
        ''''''
        RPF'(S)
        ''''''
        if self.i_am_assert_loser():
            return self._assert_winner_metric.get_ip()
        else:
            return self._kernel_entry.rpf_node
    '''

    def is_S_directly_conn(self):
        return self._kernel_entry.rpf_node == self._kernel_entry.source_ip

    ###########################################
    # Change to in/out-tree
    ###########################################
    def node_is_out_tree(self):
        return

    def node_is_in_tree(self):
        return

    ###################################################
    # ASSERT
    ###################################################
    def my_rpc_metric(self):
        rpc = self._kernel_entry._rpc # type: Metric
        return AssertMetric(rpc.metric_preference, rpc.route_metric, self.get_ip())
        #return AssertMetric.spt_assert_metric(self)

    def notify_rpc_change(self, new_rpc):
        return
