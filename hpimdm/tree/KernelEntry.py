import logging
from abc import abstractmethod
from threading import Lock, RLock

from .metric import Metric
from .tree_state import TreeState
from hpimdm import UnicastRouting
from .tree_interface import TreeInterface
from .tree_if_root import TreeInterfaceRoot
from .tree_if_non_root import TreeInterfaceNonRoot
from .tree_if_root_originator import TreeInterfaceRootOriginator


class KernelEntry:
    KERNEL_LOGGER = logging.getLogger('hpim.KernelEntry')

    def __init__(self, source_ip: str, group_ip: str, upstream_state_dic, interest_state_dic, kernel_entry_interface):
        self.kernel_entry_logger = logging.LoggerAdapter(self.KERNEL_LOGGER, {'tree': '(' + source_ip + ',' + group_ip + ')'})
        self.kernel_entry_logger.debug('Create KernelEntry')

        self.source_ip = source_ip
        self.group_ip = group_ip
        self._tree_state = TreeState.Inactive

        self._interest_interface_state = interest_state_dic
        self._upstream_interface_state = upstream_state_dic

        self._kernel_entry_interface = kernel_entry_interface

        ###### UNICAST INFO#################################################################
        (metric_administrative_distance, metric_cost, is_directly_connected, root_if) = \
            UnicastRouting.get_unicast_info(source_ip)
        # TODO verificar is directly connected
        self._rpc = Metric(metric_administrative_distance, metric_cost)
        #######################################################################################
        # Locks
        self._multicast_change = Lock()
        self._lock_test2 = RLock()
        self.CHANGE_STATE_LOCK = RLock()

        # select root interface based on rpf check
        self.inbound_interface_index = root_if
        self.interface_state = {}  # type: dict(int, TreeInterface)

    def get_inbound_interface_index(self):
        """
        Get VIF of root interface of this tree
        """
        return self.inbound_interface_index

    def get_outbound_interfaces_indexes(self):
        """
        Get OIL of this tree
        """
        return self._kernel_entry_interface.get_outbound_interfaces_indexes(self)

    @abstractmethod
    def check_tree_state(self):
        """
        Verify if tree changes state (Active/Unsure/Inactive)
        """
        return

    ################################################
    # Receive (S,G) data packets or control packets
    ################################################
    def recv_data_msg(self, index):
        """
        Receive data packet regarding this tree in interface with VIF index
        """
        print("recv data")
        self.interface_state[index].recv_data_msg()

    ###############################################################
    # Code related with tree state
    ###############################################################
    def check_interface_state(self, index, upstream_state, interest_state):
        """
        A neighbor changed Upstream state due to the reception of any control packet
        (IamUpstream or IamNoLongerUpstream or Interest or NoInterest or Sync)
        """
        if index not in self.interface_state or self.is_tree_inactive():
            return
        print("ENTER CHECK INTERFACE STATE")
        self._upstream_interface_state[index] = upstream_state

        self.interface_state[index].change_best_upstream_neighbor_state(upstream_state)
        self.check_interest_state(index, interest_state)

        self.check_tree_state()
        print("EXIT CHECK INTERFACE STATE")

    def check_interest_state(self, index, interest_state):
        """
        A neighbor changed Interest state due to the reception of any control packet
        (IamUpstream or IamNoLongerUpstream or Interest or NoInterest or Sync)
        """
        if index not in self.interface_state or self.is_tree_inactive():
            return

        current_interest_state = self._interest_interface_state.get(index, None)
        self._interest_interface_state[index] = interest_state

        if current_interest_state != interest_state:
            self.interface_state[index].change_interest_state(interest_state)

    def check_membership_state(self, index):
        """
        Reverify IGMP/MLD state of this tree in interface with VIF index...
        This is invoked whenever interface index enables or disables IGMP/MLD
        """
        print("ENTER CHECK IGMP STATE")
        if index not in self.interface_state:
            return

        self.interface_state[index].check_membership_state()
        print("EXIT CHECK IGMP STATE")

    def get_interface_sync_state(self, vif_index):
        """
        Determine if this tree must be included in a new snapshot of interface with VIF vif_index
        """
        with self.CHANGE_STATE_LOCK:
            if vif_index not in self.interface_state:
                return None
            else:
                return self.interface_state[vif_index].get_sync_state()

    def is_tree_active(self):
        """
        Determine if tree is in Active state
        """
        return self._tree_state.is_active()

    def is_tree_unsure(self):
        """
        Determine if tree is in Unsure state
        """
        return self._tree_state.is_unsure()

    def is_tree_inactive(self):
        """
        Determine if tree is in Inactive state
        """
        return self._tree_state.is_inactive()

    def set_tree_state(self, tree_state):
        """
        Set tree state (Active/Unsure/Inactive)
        """
        with self.CHANGE_STATE_LOCK:
            self.kernel_entry_logger.debug('Tree transitions to ' + str(tree_state))
            self._tree_state = tree_state

    ###############################################################
    # Unicast Changes to RPF
    ###############################################################
    @abstractmethod
    def network_update(self):
        """
        Router suffered an RPC chage... React to this change
        """
        return

    def is_in_tree(self):
        """
        Determine if router is interested in receiving data packets
        """
        for interface in self.interface_state.values():
            if interface.is_forwarding():
                return True
        return False

    @abstractmethod
    def evaluate_in_tree_change(self):
        """
        Evaluate if there is a change of interest from this router
        """
        return

    def get_source(self):
        """
        Get source IP of this tree
        """
        return self.source_ip

    def get_group(self):
        """
        Get group IP of this tree
        """
        return self.group_ip

    def change(self):
        """
        Reset multicast routing table due to changes in state
        """
        with self._multicast_change:
            if self.inbound_interface_index is not None and not self.is_tree_inactive():
                self.get_kernel().set_multicast_route(self)

    def remove_entry(self):
        """
        Remove entry from the multicast routing table
        """
        self.get_kernel().remove_multicast_route(self)

    def delete_state(self):
        """
        Delete all stored state regarding this tree
        """
        for state in self.interface_state.values():
            state.delete()
        self.interface_state.clear()

    def get_interface_name(self, interface_id):
        """
        Get name of interface from vif id
        """
        return self._kernel_entry_interface.get_interface_name(interface_id)

    def get_interface(self, interface_id):
        """
        Get HPIM interface from interface id
        """
        return self._kernel_entry_interface.get_interface(self, interface_id)

    def get_membership_interface(self, interface_id):
        """
        Get IGMP/MLD interface from interface id
        """
        return self._kernel_entry_interface.get_membership_interface(self, interface_id)

    def get_kernel(self):
        """
        Get kernel
        """
        return self._kernel_entry_interface.get_kernel()

    ######################################
    # Interface change
    #######################################
    @abstractmethod
    def new_interface(self, index):
        """
        New interface with VIF index added
        """
        return

    def remove_interface(self, index):
        """
        Interface with VIF index removed
        """
        with self.CHANGE_STATE_LOCK:
            if index not in self.interface_state:
                return

            #check if removed interface is root interface
            if self.inbound_interface_index == index:
                self.inbound_interface_index = None

            # remove cached info about removed interface
            self._upstream_interface_state.pop(index, None)
            self._interest_interface_state.pop(index, None)

            self.interface_state.pop(index).delete()
            self.change()
            self.evaluate_in_tree_change()
            self.check_tree_state()


class KernelEntryNonOriginator(KernelEntry):
    def __init__(self, source_ip: str, group_ip: str, upstream_state_dic, interest_state_dic, kernel_entry_interface):
        super().__init__(source_ip, group_ip, upstream_state_dic, interest_state_dic, kernel_entry_interface)

        # (S,G) starts OUT-TREE state... later check if node is in-tree via evaluate_in_tree_change()
        self._was_in_tree = False

        self.first_check_tree_state()
        with self.CHANGE_STATE_LOCK:
            for i in self.get_kernel().vif_index_to_name_dic.keys():
                try:
                    upstream_state = self._upstream_interface_state.get(i, None)

                    if i == self.inbound_interface_index:
                        continue
                    else:
                        interest_state = self._interest_interface_state.get(i, False)
                        self.interface_state[i] = TreeInterfaceNonRoot(self, i, self._rpc,
                                                                       best_upstream_router=upstream_state,
                                                                       interest_state=interest_state,
                                                                       was_root=False,
                                                                       previous_tree_state=TreeState.Inactive,
                                                                       current_tree_state=self._tree_state)

                except:
                    import traceback
                    print(traceback.print_exc())
                    continue
            self._was_in_tree = self.is_in_tree()
            upstream_state = self._upstream_interface_state.get(self.inbound_interface_index, None)
            if self.inbound_interface_index is not None:
                self.interface_state[self.inbound_interface_index] = \
                    TreeInterfaceRoot(self, self.inbound_interface_index, upstream_state, was_non_root=False,
                                      previous_tree_state=TreeState.Inactive, current_tree_state=self._tree_state)

        self.change()
        self.evaluate_in_tree_change()
        print('Tree NonOriginator created')

    def check_tree_state(self):
        """
        Verify if tree changes state (Active/Unsure/Inactive)
        """
        with self.CHANGE_STATE_LOCK:
            if self.inbound_interface_index is not None and \
                    len(self.interface_state) > 0 and\
                    self._upstream_interface_state.get(self.inbound_interface_index, None) is not None and \
                    (not self._rpc.is_better_than(self._upstream_interface_state.get(self.inbound_interface_index))
                     and self._rpc != self._upstream_interface_state.get(self.inbound_interface_index)):
                # tree is Active
                print("PARA ACTIVE")
                self._tree_state.transition_to_active(self)
            elif len(self.interface_state) > 0 and \
                    not all(value is None for value in self._upstream_interface_state.values()):
                print("PARA UNSURE")
                self._tree_state.transition_to_unsure(self)
            else:
                print("PARA INACTIVE")
                self._tree_state.transition_to_inactive(self)

    def first_check_tree_state(self):
        """
        Verify for the first time in which state the tree is at
        """
        if self.inbound_interface_index is not None and \
                self._upstream_interface_state.get(self.inbound_interface_index, None) is not None and \
                (not self._rpc.is_better_than(self._upstream_interface_state.get(self.inbound_interface_index))
                 and self._rpc != self._upstream_interface_state.get(self.inbound_interface_index)):
            # tree is Active
            print("PARA ACTIVE")
            self.set_tree_state(TreeState.Active)
        elif not all(value is None for value in self._upstream_interface_state.values()):
            print("PARA UNSURE")
            # tree is Unsure
            self.set_tree_state(TreeState.Unsure)
        else:
            print("PARA INACTIVE")
            # tree is Inactive
            self.set_tree_state(TreeState.Inactive)

    ###############################################################
    # Unicast Changes to RPF
    ###############################################################
    def network_update(self):
        """
        Router suffered an RPC chage... React to this change
        """
        with self.CHANGE_STATE_LOCK:
            (metric_administrative_distance, metric_cost, is_directly_connected, new_inbound_interface_index) = \
                UnicastRouting.get_unicast_info(self.source_ip)
            new_rpc = Metric(metric_administrative_distance, metric_cost)

            if is_directly_connected:
                self._tree_state.transition_to_inactive(self)
                return
            if new_inbound_interface_index != self.inbound_interface_index:
                # get old interfaces
                old_upstream_interface = self.interface_state.get(self.inbound_interface_index, None)
                old_downstream_interface = self.interface_state.get(new_inbound_interface_index, None)

                non_root_interest_state = self._interest_interface_state.get(self.inbound_interface_index, False)
                non_root_upstream_state = self._upstream_interface_state.get(self.inbound_interface_index, None)
                root_interest_state = self._interest_interface_state.get(new_inbound_interface_index, False)
                root_upstream_state = self._upstream_interface_state.get(new_inbound_interface_index, None)

                # remove old interfaces
                if old_upstream_interface is not None:
                    old_upstream_interface.delete()
                if old_downstream_interface is not None:
                    old_downstream_interface.delete()

                new_tree_state = self._tree_state
                if (self.is_tree_active() and root_upstream_state is None) or \
                        (self.is_tree_active() and root_upstream_state is not None and
                         (new_rpc.is_better_than(root_upstream_state) or new_rpc == root_upstream_state)):
                    new_tree_state = TreeState.Unsure
                elif self.is_tree_unsure() and root_upstream_state is not None and \
                        not new_rpc.is_better_than(root_upstream_state) and new_rpc != root_upstream_state:
                    new_tree_state = TreeState.Active

                # change type of interfaces
                if self.inbound_interface_index is not None:
                    new_downstream_interface = TreeInterfaceNonRoot(self, self.inbound_interface_index, new_rpc,
                                                                    non_root_upstream_state, non_root_interest_state,
                                                                    was_root=True,
                                                                    previous_tree_state=self._tree_state,
                                                                    current_tree_state=new_tree_state)
                    self.interface_state[self.inbound_interface_index] = new_downstream_interface
                if new_inbound_interface_index is not None:
                    new_upstream_interface = TreeInterfaceRoot(self, new_inbound_interface_index,
                                                               root_upstream_state, was_non_root=True,
                                                               previous_tree_state=self._tree_state,
                                                               current_tree_state=new_tree_state)
                    self.interface_state[new_inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = new_inbound_interface_index

                if self._rpc != new_rpc:
                    self._rpc = new_rpc
                    self.check_tree_state()
                    for interface in self.interface_state.values():
                        interface.notify_rpc_change(new_rpc)
                else:
                    self.check_tree_state()

                # atualizar tabela de encaminhamento multicast
                self.change()
                self.evaluate_in_tree_change()
            elif self._rpc != new_rpc:
                self._rpc = new_rpc
                self.check_tree_state()
                for interface in self.interface_state.values():
                    interface.notify_rpc_change(new_rpc)

    def evaluate_in_tree_change(self):
        """
        Evaluate if there is a change of interest from this router
        """
        with self._lock_test2:
            is_in_tree = self.is_in_tree()
            was_in_tree = self._was_in_tree
            self._was_in_tree = is_in_tree
            if was_in_tree != is_in_tree and self.inbound_interface_index is not None:
                if is_in_tree:
                    self.interface_state[self.inbound_interface_index].node_is_in_tree()
                else:
                    self.interface_state[self.inbound_interface_index].node_is_out_tree()

    #####################################################
    # New interface configured
    #####################################################
    def new_interface(self, index):
        """
        New interface with VIF index added
        """
        print("NEW_INTERFACE ANTES")
        with self.CHANGE_STATE_LOCK:
            print("NEW_INTERFACE DEPOIS")
            if index in self.interface_state:
                return

            (_, _, _, inbound_interface_index) = UnicastRouting.get_unicast_info(self.source_ip)
            # TODO verificar is directly connected

            interest_state = False
            upstream_state = None
            self._interest_interface_state[index] = interest_state
            self._upstream_interface_state[index] = upstream_state

            # new interface is of type non-root
            if inbound_interface_index != index:
                self.interface_state[index] = TreeInterfaceNonRoot(self, index, self._rpc,
                                                                   best_upstream_router=upstream_state,
                                                                   interest_state=interest_state,
                                                                   was_root=False,
                                                                   previous_tree_state=self._tree_state,
                                                                   current_tree_state=self._tree_state)
            # new interface is of type root and there wasnt any root interface previously configured
            elif inbound_interface_index == index and self.inbound_interface_index is None:
                self.inbound_interface_index = index
                self.interface_state[index] = TreeInterfaceRoot(self, self.inbound_interface_index,
                                                                upstream_state, was_non_root=False,
                                                                previous_tree_state=self._tree_state,
                                                                current_tree_state=self._tree_state)
            # new interface is of type root and there was a root interface previously configured
            elif inbound_interface_index == index and self.inbound_interface_index is not None:
                old_upstream_interface = self.interface_state.get(self.inbound_interface_index, None)

                root_upstream_state = upstream_state
                non_root_interest_state = self._interest_interface_state.get(self.inbound_interface_index, False)
                non_root_upstream_state = self._upstream_interface_state.get(self.inbound_interface_index, None)

                new_tree_state = self._tree_state
                if self.is_tree_active() and root_upstream_state is None:
                    new_tree_state = TreeState.Unsure

                # change type of interfaces
                if self.inbound_interface_index is not None:
                    new_downstream_interface = TreeInterfaceNonRoot(self, self.inbound_interface_index, self._rpc,
                                                                    non_root_upstream_state, non_root_interest_state,
                                                                    was_root=True,
                                                                    previous_tree_state=self._tree_state,
                                                                    current_tree_state=new_tree_state)
                    self.interface_state[self.inbound_interface_index] = new_downstream_interface
                if inbound_interface_index is not None:
                    new_upstream_interface = TreeInterfaceRoot(self, inbound_interface_index, root_upstream_state,
                                                               was_non_root=True,
                                                               previous_tree_state=self._tree_state,
                                                               current_tree_state=new_tree_state)
                    self.interface_state[inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = inbound_interface_index

                # remove old interfaces
                if old_upstream_interface is not None:
                    old_upstream_interface.delete()

            self.change()
            self.evaluate_in_tree_change()
            self.check_tree_state()


class KernelEntryOriginator(KernelEntry):
    KERNEL_LOGGER = logging.getLogger('hpim.KernelEntryOriginator')

    def __init__(self, source_ip: str, group_ip: str, upstream_state_dic, interest_state_dic, kernel_entry_interface):
        super().__init__(source_ip, group_ip, upstream_state_dic, interest_state_dic, kernel_entry_interface)
        self.sat_is_running = False
        if self.inbound_interface_index is not None:
            self.sat_is_running = True
            self.set_tree_state(TreeState.Active)
        else:
            self.set_tree_state(TreeState.Unsure)

        with self.CHANGE_STATE_LOCK:
            for i in self.get_kernel().vif_index_to_name_dic.keys():
                try:
                    upstream_state = self._upstream_interface_state.get(i, None)

                    if i != self.inbound_interface_index:
                        interest_state = self._interest_interface_state.get(i, False)
                        self.interface_state[i] = TreeInterfaceNonRoot(self, i, self._rpc,
                                                                       best_upstream_router=upstream_state,
                                                                       interest_state=interest_state,
                                                                       was_root=False,
                                                                       previous_tree_state=TreeState.Inactive,
                                                                       current_tree_state=self._tree_state)
                except:
                    import traceback
                    print(traceback.print_exc())
                    continue

            if self.inbound_interface_index is not None:
                self.interface_state[self.inbound_interface_index] = \
                    TreeInterfaceRootOriginator(self, self.inbound_interface_index, self._tree_state)

        self.change()
        self.check_tree_state()
        print('Tree Originator created')

    def check_tree_state(self):
        """
        Verify if tree changes state (Active/Unsure/Inactive)
        """
        if self.inbound_interface_index is not None and self.sat_is_running and len(self.interface_state) > 0:
            print("PARA ACTIVE")
            # tree is active
            self._tree_state.transition_to_active(self)
        elif len(self.interface_state) == 0 or\
                (not self.sat_is_running and all(v is None for v in self._upstream_interface_state.values())):
            # tree is Inactive
            print("PARA INACTIVE")
            self._tree_state.transition_to_inactive(self)
        elif self.inbound_interface_index is None or not self.sat_is_running:
            print("PARA UNSURE")
            # tree is Unsure
            self._tree_state.transition_to_unsure(self)

    ###############################################################
    # Code related with tree state
    ###############################################################
    def sat_expires(self):
        """
        Source Active has expired
        """
        self.sat_is_running = False
        self.check_tree_state()

    def sat_running(self):
        """
        Source Active timer was set
        """
        self.sat_is_running = True
        self.check_tree_state()

    ###############################################################
    # Unicast Changes to RPF
    ###############################################################
    def network_update(self):
        """
        Router suffered an RPC chage... React to this change
        """
        with self.CHANGE_STATE_LOCK:
            (metric_administrative_distance, metric_cost, is_directly_connected, new_inbound_interface_index) = \
                UnicastRouting.get_unicast_info(self.source_ip)
            new_rpc = Metric(metric_administrative_distance, metric_cost)

            if not is_directly_connected:
                self._tree_state.transition_to_inactive(self)
                return
            if new_inbound_interface_index != self.inbound_interface_index:
                # get old interfaces
                old_upstream_interface = self.interface_state.get(self.inbound_interface_index, None)
                old_downstream_interface = self.interface_state.get(new_inbound_interface_index, None)

                non_root_interest_state = self._interest_interface_state.get(self.inbound_interface_index, False)
                non_root_upstream_state = self._upstream_interface_state.get(self.inbound_interface_index, None)
                root_interest_state = self._interest_interface_state.get(new_inbound_interface_index, False)
                root_upstream_state = self._upstream_interface_state.get(new_inbound_interface_index, None)

                if new_inbound_interface_index is None:
                    self.sat_is_running = False
                    new_tree_state = TreeState.Unsure
                else:
                    new_tree_state = TreeState.Active

                # change type of interfaces
                if self.inbound_interface_index is not None:
                    new_downstream_interface = TreeInterfaceNonRoot(self, self.inbound_interface_index, self._rpc,
                                                                    non_root_upstream_state, non_root_interest_state,
                                                                    was_root=True,
                                                                    previous_tree_state=self._tree_state,
                                                                    current_tree_state=new_tree_state)
                    self.interface_state[self.inbound_interface_index] = new_downstream_interface
                if new_inbound_interface_index is not None:
                    self.sat_is_running = True
                    new_upstream_interface = TreeInterfaceRootOriginator(self, new_inbound_interface_index, new_tree_state)
                    self.interface_state[new_inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = new_inbound_interface_index

                # remove old interfaces
                if old_upstream_interface is not None:
                    old_upstream_interface.delete()
                if old_downstream_interface is not None:
                    old_downstream_interface.delete()

                self.check_tree_state()
                self.change()
            if self._rpc != new_rpc:
                self._rpc = new_rpc
                for interface in self.interface_state.values():
                    interface.notify_rpc_change(new_rpc)

    def evaluate_in_tree_change(self):
        """
        Evaluate if there is a change of interest from this router
        """
        return

    #####################################################
    # New interface configured
    #####################################################
    def new_interface(self, index):
        """
        New interface with VIF index added
        """
        print("NEW_INTERFACE ANTES")
        with self.CHANGE_STATE_LOCK:
            print("NEW_INTERFACE DEPOIS")
            if index in self.interface_state:
                return

            (_, _, _, inbound_interface_index) = UnicastRouting.get_unicast_info(self.source_ip)
            # TODO verificar is directly connected
            interest_state = False
            upstream_state = None
            self._interest_interface_state[index] = interest_state
            self._upstream_interface_state[index] = upstream_state

            if inbound_interface_index != index:
                self.interface_state[index] = TreeInterfaceNonRoot(self, index, self._rpc,
                                                                   best_upstream_router=upstream_state,
                                                                   interest_state=interest_state,
                                                                   was_root=False,
                                                                   previous_tree_state=self._tree_state,
                                                                   current_tree_state=self._tree_state)
            elif inbound_interface_index == index and self.inbound_interface_index is None:
                self.inbound_interface_index = index
                self.sat_is_running = True
                self.interface_state[index] = \
                    TreeInterfaceRootOriginator(self, self.inbound_interface_index, self._tree_state)
            elif inbound_interface_index == index and self.inbound_interface_index is not None:
                old_upstream_interface = self.interface_state.get(self.inbound_interface_index, None)
                non_root_interest_state = self._interest_interface_state.get(self.inbound_interface_index, False)
                non_root_upstream_state = self._upstream_interface_state.get(self.inbound_interface_index, None)

                # change type of interfaces
                if self.inbound_interface_index is not None:
                    new_downstream_interface = TreeInterfaceNonRoot(self, self.inbound_interface_index, self._rpc,
                                                                    non_root_upstream_state, non_root_interest_state,
                                                                    was_root=True,
                                                                    previous_tree_state=self._tree_state,
                                                                    current_tree_state=self._tree_state)
                    self.interface_state[self.inbound_interface_index] = new_downstream_interface
                if inbound_interface_index is not None:
                    self.sat_is_running = True
                    new_upstream_interface = TreeInterfaceRootOriginator(self, inbound_interface_index,
                                                                         self._tree_state)
                    self.interface_state[inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = inbound_interface_index

                # remove old interfaces
                if old_upstream_interface is not None:
                    old_upstream_interface.delete()

            self.change()
            self.evaluate_in_tree_change()

    def remove_interface(self, index):
        """
        Interface with VIF index removed
        """
        with self.CHANGE_STATE_LOCK:
            super().remove_interface(index)
            if self.inbound_interface_index is None:
                self.sat_is_running = False
                self.check_tree_state()
