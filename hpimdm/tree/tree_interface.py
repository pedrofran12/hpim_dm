import logging
import ipaddress
from threading import RLock
from abc import ABCMeta, abstractmethod

from .tree_state import TreeState
from .local_membership import LocalMembership


class TreeInterface(metaclass=ABCMeta):
    def __init__(self, kernel_entry, interface_id, best_upstream_router, current_tree_state, logger: logging.LoggerAdapter):
        self._kernel_entry = kernel_entry
        self._interface_id = interface_id
        self.logger = logger

        self._best_upstream_router = best_upstream_router  # current assert winner

        self.current_tree_state = current_tree_state  # current tree state

        # Local Membership State
        self._igmp_lock = RLock()
        try:
            membership_interface = self.get_membership_interface()  # type: InterfaceIGMP
            group_state = membership_interface.interface_state.get_group_state(kernel_entry.group_ip)
            has_members = group_state.add_multicast_routing_entry(self)
            self._local_membership_state = LocalMembership.Include if has_members else LocalMembership.NoInfo
        except:
            self._local_membership_state = LocalMembership.NoInfo

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        """
        This interface received a data packet
        """
        pass

    ######################################
    # Send messages
    ######################################
    def get_sync_state(self):
        """
        Determine if this tree must be included in a new snapshot
        By default not include this tree in snapshot... This behavior is overrode by subclasses (in NonRoot interfaces)
        """
        return None

    def send_i_am_no_longer_upstream(self):
        """
        Send an IamNoLongerUpstream message through this interface
        """
        (source, group) = self.get_tree_id()
        if self.get_interface() is not None:
            self.get_interface().send_i_am_no_longer_upstream(source, group)

    def send_interest(self):
        """
        Send an Interest message through this interface
        """
        (source, group) = self.get_tree_id()
        best_upstream_neighbor = self._best_upstream_router.get_ip()
        if self.get_interface() is not None:
            self.get_interface().send_interest(source, group, best_upstream_neighbor)

    def send_no_interest(self):
        """
        Send a NoInterest message through this interface
        """
        (source, group) = self.get_tree_id()
        best_upstream_neighbor = self._best_upstream_router.get_ip()
        if self.get_interface() is not None:
            self.get_interface().send_no_interest(source, group, best_upstream_neighbor)

    def is_tree_active(self):
        """
        Verify if this interface considers the tree to be in Active state
        """
        return self.current_tree_state.is_active()

    def is_tree_unsure(self):
        """
        Verify if this interface considers the tree to be in Unsure state
        """
        return self.current_tree_state.is_unsure()

    def is_tree_inactive(self):
        """
        Verify if this interface considers the tree to be in Inactive state
        """
        return self.current_tree_state.is_inactive()

    #############################################################
    @abstractmethod
    def is_forwarding(self):
        """
        Determine if this interface must be included in the OIL at the multicast routing table...
        This method must be overrode by subclasses
        """
        pass

    @abstractmethod
    def delete(self):
        """
        Tree interface is being removed... due to change of interface roles or
        due to the removal of the tree by this router
        Clear all state from this interface regarding this tree
        """
        (s, g) = self.get_tree_id()
        # unsubscribe igmp information
        try:
            membership_interface = self.get_membership_interface()  # type: InterfaceIGMP
            group_state = membership_interface.interface_state.get_group_state(g)
            group_state.remove_multicast_routing_entry(self)
        except:
            pass

        print('Tree Interface deleted')

    def is_node_in_tree(self):
        """
        Determine if this router is interested in receiving data packets
        """
        return self._kernel_entry.is_in_tree()

    def evaluate_in_tree(self):
        """
        Verify if there are changes regarding interest of the router...
        This method is invoked whenever a new interface is included in the OIL or if an interface is removed from it
        """
        self._kernel_entry.evaluate_in_tree_change()

    ############################################################
    # Assert Winner state
    ############################################################
    def calculate_assert_winner(self):
        """
        Calculate the router responsible for forwarding data packets to a link...
        This method must be overrode by subclasses
        """
        return

    def change_best_upstream_neighbor_state(self, new_best_upstream_neighbor_state):
        """
        A neighbor changed Upstream state due to the reception of any control packet
        (IamUpstream or IamNoLongerUpstream or Interest or NoInterest or Sync)
        """
        self._best_upstream_router = new_best_upstream_neighbor_state

    ###########################################################
    # Interest state
    ###########################################################
    def change_interest_state(self, interest_state):
        """
        A neighbor has changed Interest state due to the reception of any control packet
        (IamUpstream or IamNoLongerUpstream or Interest or NoInterest or Sync)
        """
        return

    ##########################################################
    # Tree transitions
    ##########################################################
    def tree_transition_to_active(self):
        """
        The tree of this interface detected that the tree transitioned to Active state
        The interface must react to this change in order to send some control messages
        """
        self.current_tree_state = TreeState.Active

    def tree_transition_to_unsure(self):
        """
        The tree of this interface detected that the tree transitioned to Unsure state
        The interface must react to this change in order to send some control messages
        """
        self.current_tree_state = TreeState.Unsure

    def tree_transition_to_inactive(self):
        """
        The tree of this interface detected that the tree transitioned to Inactive state
        The interface must react to this change in order to send some control messages
        """
        self.current_tree_state = TreeState.Inactive


    #############################################################
    # Local Membership (IGMP/MLD)
    ############################################################
    def check_membership_state(self):
        """
        Reverify IGMP/MLD state of this group whenever this interface enabled or disabled IGMP/MLD
        """
        (_, group_ip) = self.get_tree_id()
        with self._igmp_lock:
            try:
                membership_interface = self.get_membership_interface()  # type: InterfaceIGMP
                group_state = membership_interface.interface_state.get_group_state(group_ip)
                has_members = group_state.add_multicast_routing_entry(self)
                self._local_membership_state = LocalMembership.Include if has_members else LocalMembership.NoInfo
            except:
                self._local_membership_state = LocalMembership.NoInfo
            self.change_tree()
            self.evaluate_in_tree()

    def notify_membership(self, has_members: bool):
        """
        IGMP/MLD detected a change of membership regarding the group of this tree
        """
        with self.get_state_lock():
            with self._igmp_lock:
                if has_members != self._local_membership_state.has_members():
                    self._local_membership_state = LocalMembership.Include if has_members else LocalMembership.NoInfo
                    self.change_tree()
                    self.evaluate_in_tree()

    def local_membership_has_members(self):
        """
        Determine if there are hosts interested in receiving data packets regarding this tree
        """
        with self._igmp_lock:
            return self._local_membership_state.has_members()

    def get_interface(self):
        """
        Get the InterfaceHPIM object regarding this physical interface
        """
        return self._kernel_entry.get_interface(self._interface_id)

    def get_membership_interface(self):
        """
        Get InterfaceIGMP or InterfaceMLD object regarding this physical interface
        """
        return self._kernel_entry.get_membership_interface(self._interface_id)

    def get_interface_name(self):
        """
        Get interface name of this interface
        """
        return self._kernel_entry.get_interface_name(self._interface_id)

    def get_ip(self):
        """
        Get IP of this interface
        """
        interface = self.get_interface()
        if interface is not None:
            return interface.get_ip()
        return "0.0.0.0"

    def get_all_interface_networks(self):
        """
        Get all networks associated with interface
        More than one can be associated for example in the case of IPv6 (link local + global + unique local)
        """
        interface = self.get_interface()
        if interface is not None:
            return interface.get_all_interface_networks()
        return {"0.0.0.0/32"}

    def is_interface_connected_to_source(self):
        """
        Determine if this interface is connected to the source of multicast traffic
        """
        source_ip = self.get_tree_id()[0]
        for network in self.get_all_interface_networks():
            if ipaddress.ip_address(source_ip) in ipaddress.ip_network(network):
                return True
        return False

    def get_tree_id(self):
        """
        Get tree id, i.e. pair (Source, Group) IPs
        """
        return (self._kernel_entry.source_ip, self._kernel_entry.group_ip)

    def change_tree(self):
        """
        Re-set multicast routing table...
        Invoked whenever there are state transitions
        """
        self._kernel_entry.change()

    def get_state_lock(self):
        """
        Obtain lock used to change state of an interface
        """
        return self._kernel_entry.CHANGE_STATE_LOCK

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
