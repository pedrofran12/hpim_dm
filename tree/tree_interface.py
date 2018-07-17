from abc import ABCMeta, abstractmethod
import Main
from threading import RLock
from .metric import AssertMetric, Metric
from .local_membership import LocalMembership
import logging

class TreeInterface(metaclass=ABCMeta):
    def __init__(self, kernel_entry, interface_id, best_upstream_router, current_tree_state, logger: logging.LoggerAdapter):
        self._kernel_entry = kernel_entry
        self._interface_id = interface_id
        self.logger = logger

        self._best_upstream_router = best_upstream_router # current assert winner

        self.current_tree_state = current_tree_state # current tree state

        # Local Membership State
        self._igmp_lock = RLock()
        try:
            interface_name = Main.kernel.vif_index_to_name_dic[interface_id]
            igmp_interface = Main.igmp_interfaces[interface_name]  # type: InterfaceIGMP
            group_state = igmp_interface.interface_state.get_group_state(kernel_entry.group_ip)
            igmp_has_members = group_state.add_multicast_routing_entry(self)
            self._local_membership_state = LocalMembership.Include if igmp_has_members else LocalMembership.NoInfo
        except:
            self._local_membership_state = LocalMembership.NoInfo


    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        pass

    ######################################
    # Send messages
    ######################################
    def get_sync_state(self):
        return None

    def send_i_am_no_longer_upstream(self):
        (source, group) = self.get_tree_id()
        if self.get_interface() is not None:
            self.get_interface().send_i_am_no_longer_upstream(source, group)

    def send_interest(self):
        (source, group) = self.get_tree_id()
        best_upstream_neighbor = self._best_upstream_router.get_ip()
        if self.get_interface() is not None:
            self.get_interface().send_interest(source, group, best_upstream_neighbor)

    def send_no_interest(self):
        (source, group) = self.get_tree_id()
        best_upstream_neighbor = self._best_upstream_router.get_ip()
        if self.get_interface() is not None:
            self.get_interface().send_no_interest(source, group, best_upstream_neighbor)

    def is_tree_active(self):
        return self.current_tree_state.is_active()

    def is_tree_inactive(self):
        return self.current_tree_state.is_inactive()

    def is_tree_unknown(self):
        return self.current_tree_state.is_unknown()

    #############################################################
    @abstractmethod
    def is_forwarding(self):
        pass

    @abstractmethod
    def delete(self):
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


    ############################################################
    # Assert Winner state
    ############################################################
    def calculate_assert_winner(self):
        return

    def change_assert_state(self, assert_state):
        self._best_upstream_router = assert_state

    ###########################################################
    # Interest state
    ###########################################################
    def change_interest_state(self, interest_state):
        return


    ##########################################################
    # Tree transitions
    ##########################################################
    def tree_transition_to_active(self):
        from .KernelEntry import ActiveTree
        self.current_tree_state = ActiveTree

    def tree_transition_to_inactive(self):
        from .KernelEntry import InactiveTree
        self.current_tree_state = InactiveTree

    def tree_transition_to_unknown(self):
        from .KernelEntry import UnknownTree
        self.current_tree_state = UnknownTree


    #############################################################
    # Local Membership (IGMP)
    ############################################################
    def check_igmp_state(self):
        (_, group_ip) = self.get_tree_id()
        with self._igmp_lock:
            try:
                interface_name = Main.kernel.vif_index_to_name_dic[self._interface_id]
                igmp_interface = Main.igmp_interfaces[interface_name]  # type: InterfaceIGMP
                group_state = igmp_interface.interface_state.get_group_state(group_ip)
                #self._igmp_has_members = group_state.add_multicast_routing_entry(self)
                igmp_has_members = group_state.add_multicast_routing_entry(self)
                self._local_membership_state = LocalMembership.Include if igmp_has_members else LocalMembership.NoInfo
            except:
                self._local_membership_state = LocalMembership.NoInfo
            self.change_tree()
            self.evaluate_in_tree()


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
        #with Main.kernel.interface_lock:
        interface = Main.interfaces.get(self.get_interface_name(), None)
        return interface

    def get_interface_name(self):
        kernel = Main.kernel
        return kernel.vif_index_to_name_dic.get(self._interface_id, None)

    def get_ip(self):
        #ip = self.get_interface().get_ip()
        if_name = Main.kernel.vif_index_to_name_dic[self._interface_id]
        import netifaces
        ip = netifaces.ifaddresses(if_name)[netifaces.AF_INET][0]['addr']
        return ip

    def get_tree_id(self):
        return (self._kernel_entry.source_ip, self._kernel_entry.group_ip)

    def change_tree(self):
        self._kernel_entry.change()

    def get_state_lock(self):
        return self._kernel_entry.CHANGE_STATE_LOCK

    @abstractmethod
    def is_downstream(self):
        raise NotImplementedError()

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
    # RPC Change
    ###################################################
    def notify_rpc_change(self, new_rpc):
        return
