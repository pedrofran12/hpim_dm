from tree.tree_if_upstream import TreeInterfaceUpstream
from tree.tree_if_downstream import TreeInterfaceDownstream
from .tree_interface import TreeInterface
from threading import Timer, Lock, RLock
from tree.metric import AssertMetric, Metric
import UnicastRouting
from time import time
import Main
import logging

class TreeState:
    @staticmethod
    def transition_to_active(kernel_entry):
        return

    @staticmethod
    def transition_to_inactive(kernel_entry):
        return

    @staticmethod
    def transition_to_unknown(kernel_entry):
        return

class ActiveTree(TreeState):
    @staticmethod
    def transition_to_inactive(kernel_entry):
        for interface in kernel_entry.interface_state.values():
            #interface.
            break
        return

    @staticmethod
    def transition_to_unknown(kernel_entry):
        return


class InactiveTree(TreeState):
    @staticmethod
    def transition_to_active(kernel_entry):
        return

    @staticmethod
    def transition_to_unknown(kernel_entry):
        return

class UnknownTree(TreeState):
    @staticmethod
    def transition_to_active(kernel_entry):
        return

    @staticmethod
    def transition_to_inactive(kernel_entry):
        return


class KernelEntry:
    KERNEL_LOGGER = logging.getLogger('protocol.KernelEntry')

    def __init__(self, source_ip: str, group_ip: str):
        self.kernel_entry_logger = logging.LoggerAdapter(KernelEntry.KERNEL_LOGGER, {'tree': '(' + source_ip + ',' + group_ip + ')'})
        self.kernel_entry_logger.debug('Create KernelEntry')

        self.source_ip = source_ip
        self.group_ip = group_ip


        self._tree_state = UnknownTree


        self._interest_interface_state = {}
        self._upstream_interface_state = {}
        self._inactive_interfaces_that_are_ready = {}
        # ip of neighbor of the rpf
        #next_hop = UnicastRouting.get_route(source_ip)["gateway"]
        #self.rpf_node = source_ip if next_hop is None else next_hop

        '''
        next_hop = UnicastRouting.get_route(source_ip)["gateway"]
        multipaths = UnicastRouting.get_route(source_ip)["multipath"]

        self.rpf_node = next_hop if next_hop is not None else source_ip
        print("MUL", multipaths)
        #self.rpf_node = multipaths[0]["gateway"]
        for m in multipaths:
            if m["gateway"] is None:
                self.rpf_node = source_ip
                break
            else:
                self.rpf_node = m["gateway"]
        '''
        unicast_route = UnicastRouting.get_route(source_ip)
        next_hop = unicast_route["gateway"]
        multipaths = unicast_route["multipath"]

        self.rpf_node = next_hop if next_hop is not None else source_ip
        import ipaddress
        highest_ip = ipaddress.ip_address("0.0.0.0")
        for m in multipaths:
            if m["gateway"] is None:
                self.rpf_node = source_ip
                break
            elif ipaddress.ip_address(m["gateway"]) > highest_ip:
                highest_ip = ipaddress.ip_address(m["gateway"])
                self.rpf_node = m["gateway"]

        print("RPF_NODE:", UnicastRouting.get_route(source_ip))
        print(self.rpf_node == source_ip)
        metric_administrative_distance = unicast_route["proto"]
        metric_cost = unicast_route["priority"]
        metric_cost = metric_cost if metric_cost is not None else 0
        self._rpc = Metric(metric_administrative_distance, metric_cost)

        # (S,G) starts OUT-TREE state... later check if node is in-tree via evaluate_in_tree_change()
        self._was_in_tree = False

        # Locks
        self._multicast_change = Lock()
        self._lock_test2 = RLock()
        self.CHANGE_STATE_LOCK = RLock()

        # decide inbound interface based on rpf check
        self.inbound_interface_index = Main.kernel.vif_dic[self.check_rpf()]

        self.interface_state = {}  # type: Dict[int, TreeInterface]
        with self.CHANGE_STATE_LOCK:
            for i in Main.kernel.vif_index_to_name_dic.keys():
                try:
                    if i == self.inbound_interface_index:
                        self.interface_state[i] = TreeInterfaceUpstream(self, i, None)
                    else:
                        self.interface_state[i] = TreeInterfaceDownstream(self, i, self._rpc)
                    self._upstream_interface_state[i] = None
                    self._interest_interface_state[i] = False
                    self._inactive_interfaces_that_are_ready[i] = False
                except:
                    import traceback
                    print(traceback.print_exc())
                    continue

        self.change()
        self.evaluate_in_tree_change()
        print('Tree created')

        if self.interface_state[self.inbound_interface_index].is_S_directly_conn():
            self.change_tree_to_active_state()
        #self._lock = threading.RLock()


    def get_inbound_interface_index(self):
        return self.inbound_interface_index

    def get_outbound_interfaces_indexes(self):
        outbound_indexes = [0]*Main.kernel.MAXVIFS
        for (index, state) in self.interface_state.items():
            outbound_indexes[index] = state.is_forwarding()
        return outbound_indexes

    def check_rpf(self):
        return UnicastRouting.check_rpf(self.source_ip)


    ################################################
    # Receive (S,G) data packets or control packets
    ################################################
    def recv_data_msg(self, index):
        print("recv data")
        self.interface_state[index].recv_data_msg()

    '''
    def recv_assert_msg(self, index, packet):
        print("recv assert")
        pkt_assert = packet.payload.payload
        metric = pkt_assert.metric
        metric_preference = pkt_assert.metric_preference
        assert_sender_ip = packet.ip_header.ip_src

        received_metric = AssertMetric(metric_preference=metric_preference, route_metric=metric, ip_address=assert_sender_ip)
        self.interface_state[index].recv_assert_msg(received_metric)
    '''
    '''
    def recv_interest_msg(self, index, packet):
        print("recv join msg")
        sender_ip = packet.ip_header.ip_src
        pkt_join = packet.payload.payload

        #from .downstream_nodes_state_entry import StateEntry
        #state = StateEntry(sender_ip, "J", pkt_join.counter)
        #self.interface_state[index].recv_join_msg(state)
        #self.interface_state[index].check_downstream_interest()
        self.interface_state[index].recv_interest_msg(sender_ip)


    def recv_no_interest_msg(self, index, packet):
        print("recv prune msg")
        sender_ip = packet.ip_header.ip_src
        pkt_prune = packet.payload.payload

        #from .downstream_nodes_state_entry import StateEntry
        #state = StateEntry(sender_ip, "P", pkt_prune.counter)
        #self.interface_state[index].recv_prune_msg(state)
        #self.interface_state[index].check_downstream_interest()
        self.interface_state[index].recv_no_interest_msg(sender_ip)
    '''
    '''
    def recv_quack_msg(self, index, packet):
        print("recv quack msg")
        sender_ip = packet.ip_header.ip_src
        pkt_prune_l = packet.payload.payload
        self.interface_state[index].recv_quack_msg(sender_ip, pkt_prune_l.states)
    '''
    '''
    def recv_install_msg(self, index, packet):
        print("recv install msg")
        sender_ip = packet.ip_header.ip_src
        pkt_install = packet.payload.payload

        metric = pkt_install.metric
        metric_preference = pkt_install.metric_preference
        assert_sender_ip = packet.ip_header.ip_src

        received_metric = AssertMetric(metric_preference=metric_preference, route_metric=metric, ip_address=assert_sender_ip)
        self.interface_state[index].recv_install_msg(sender_ip, received_metric)
        #self.interface_state[index].check_aw()
        #self.check_interface_state()


    def recv_uninstall_msg(self, index, packet):
        print("recv uninstall msg")
        sender_ip = packet.ip_header.ip_src
        pkt_uninstall = packet.payload.payload
        self.interface_state[index].recv_uninstall_msg(sender_ip)
        #self.check_interface_state()

    '''

    def recv_ack_msg(self, index, packet):
        print("recv ack msg")
        sender_ip = packet.ip_header.ip_src
        pkt_ack = packet.payload.payload
        acked_sequence_number = pkt_ack.sequence_number
        self.interface_state[index].recv_ack_msg(sender_ip, acked_sequence_number)

    ###############################################################
    # Check tree state (Active or Inactive or Unknown)
    ###############################################################
    '''
    def check_interface_state(self):
        root_interface = self.interface_state[self.inbound_interface_index]
        if root_interface.has_upstream_neighbors():
            self._tree_state.transition_to_active(self)
        else:
            for (index, interface) in self.interface_state.items():
                if index != self.inbound_interface_index and interface.has_upstream_neighbors():
                    self._tree_state.transition_to_inactive(self)
                    return
        self._tree_state.transition_to_unknown(self)
    '''


    #################
    # MINHAS ALTERACOES
    # TODO
    # TODO
    # TODO
    def check_interface_state(self, index, upstream_state, interest_state):
        self._upstream_interface_state[index] = upstream_state

        # todo criar metodo change_state
        self.interface_state[index].change_assert_state(upstream_state)
        self.check_interest_state(index, interest_state)


        if all(value is None for value in self._upstream_interface_state.values()) and not self.interface_state[self.inbound_interface_index].is_S_directly_conn():
            # tree is unknown
            print("PARA UNKNOWN")
            self.change_tree_to_unknown_state()
        elif self.inbound_interface_index == index and not self.interface_state[self.inbound_interface_index].is_S_directly_conn():
            if upstream_state is None:
                # todo transitar para estado inativo (no caso de nao estar)
                print("PARA INACTIVO")
                self.change_tree_to_inactive_state()
            else:
                # todo transitar para estado ativo (no caso de nao estar)
                print("PARA ACTIVO")
                self.change_tree_to_active_state()

    def check_interest_state(self, index, interest_state):
        current_interest_state = self._interest_interface_state.get(index, None)
        self._interest_interface_state[index] = interest_state

        # todo criar metodo change_interest_state
        if current_interest_state != interest_state:
            self.interface_state[index].change_interest_state(interest_state)

    def is_tree_active(self):
        with self.CHANGE_STATE_LOCK:
            return self._tree_state == ActiveTree

    def is_tree_inactive(self):
        with self.CHANGE_STATE_LOCK:
            return self._tree_state == InactiveTree

    def is_tree_unknown(self):
        with self.CHANGE_STATE_LOCK:
            return self._tree_state == UnknownTree


    def change_tree_to_unknown_state(self):
        with self.CHANGE_STATE_LOCK:
            # TODO alterar isto
            if self._tree_state == UnknownTree:
                return
            else:
                old_state = self._tree_state
                self._tree_state = UnknownTree

                if old_state == ActiveTree:
                    #self._inactive_interfaces_that_are_ready = {}
                    for (index, interface) in self.interface_state.items():
                        #self._inactive_interfaces_that_are_ready[index] = False
                        interface.transition_to_inactive()
                elif old_state == InactiveTree:
                    # check if already can delete entry
                    if False not in self._inactive_interfaces_that_are_ready.values():
                        self.remove_entry()
                        return


            #self.change()
            #self.evaluate_in_tree_change()

    def change_tree_to_inactive_state(self):
        with self.CHANGE_STATE_LOCK:
            # TODO alterar isto
            if self._tree_state == InactiveTree:
                return

            # todo determinar se inativo ou unknown
            self._tree_state = InactiveTree
            #self._inactive_interfaces_that_are_ready = {}
            for (index, interface) in self.interface_state.items():
                #self._inactive_interfaces_that_are_ready[index] = False
                print("INTERFACE ", index, "PARA INATIVO")
                interface.transition_to_inactive()

            self.change()
            self.evaluate_in_tree_change()

    def change_tree_to_active_state(self):
        with self.CHANGE_STATE_LOCK:
            if self._tree_state == ActiveTree:
                return
            #if self.is_tree_active():
            #    return

            self._tree_state = ActiveTree
            #self._inactive_interfaces_that_are_ready = {}
            for (index, interface) in self.interface_state.items():
                print("INTERFACE ", index, "PARA ATIVO")
                self._inactive_interfaces_that_are_ready[index] = False
                interface.transition_to_active()

            self.change()
            self.evaluate_in_tree_change()

    def notify_interface_is_ready_to_remove(self, index):
        # todo ver melhor lock
        with self.CHANGE_STATE_LOCK:
            if self._tree_state == ActiveTree:
                return

            print("NOTIFY REMOVE: ", index)
            self._inactive_interfaces_that_are_ready[index] = True

            print("INTERFACES NOT READY??: ", False in self._inactive_interfaces_that_are_ready.values())
            if False in self._inactive_interfaces_that_are_ready.values():
                return

        #self.delete()
            if self.is_tree_unknown():
                self.remove_entry()

    def get_interface_sync_state(self, vif_index):
        with self.CHANGE_STATE_LOCK:
            if self._tree_state != ActiveTree:
                return None
            else:
                return self.interface_state[vif_index].get_sync_state()

    def are_there_upstream_nodes(self):
        return not all(value is None for value in self._upstream_interface_state.values())

    ###############################################################
    # Unicast Changes to RPF
    ###############################################################
    def network_update(self):
        # TODO TALVEZ OUTRO LOCK PARA BLOQUEAR ENTRADA DE PACOTES
        with self.CHANGE_STATE_LOCK:
            '''
            next_hop = UnicastRouting.get_route(self.source_ip)["gateway"]
            multipaths = UnicastRouting.get_route(self.source_ip)["multipath"]

            rpf_node = next_hop
            print("MUL", multipaths)
            # self.rpf_node = multipaths[0]["gateway"]
            for m in multipaths:
                if m["gateway"] is None:
                    rpf_node = self.source_ip
                    break
                else:
                    rpf_node = m["gateway"]
            '''
            unicast_route = UnicastRouting.get_route(self.source_ip)
            next_hop = unicast_route["gateway"]
            multipaths = unicast_route["multipath"]

            rpf_node = next_hop if next_hop is not None else self.source_ip
            import ipaddress
            highest_ip = ipaddress.ip_address("0.0.0.0")
            for m in multipaths:
                if m["gateway"] is None:
                    rpf_node = self.source_ip
                    break
                elif ipaddress.ip_address(m["gateway"]) > highest_ip:
                    highest_ip = ipaddress.ip_address(m["gateway"])
                    rpf_node = m["gateway"]

            print("RPF_NODE:", UnicastRouting.get_route(self.source_ip))
            print(self.rpf_node == self.source_ip)
            metric_administrative_distance = unicast_route["proto"]
            metric_cost = unicast_route["priority"]
            metric_cost = metric_cost if metric_cost is not None else 0
            new_rpc = Metric(metric_administrative_distance, metric_cost)

            new_inbound_interface_index = Main.kernel.vif_dic.get(self.check_rpf(), None)
            if new_inbound_interface_index is None:
                #self.delete()
                self.remove_entry()
                return
            if new_inbound_interface_index != self.inbound_interface_index:
                self.rpf_node = rpf_node

                # get old interfaces
                old_upstream_interface = self.interface_state[self.inbound_interface_index]
                old_downstream_interface = self.interface_state[new_inbound_interface_index]

                non_root_interest_state = self._interest_interface_state.get(self.inbound_interface_index, False)
                non_root_upstream_state = self._upstream_interface_state.get(self.inbound_interface_index, None)
                root_interest_state = self._interest_interface_state.get(new_inbound_interface_index, False)
                root_upstream_state = self._upstream_interface_state.get(new_inbound_interface_index, None)

                # change type of interfaces
                new_downstream_interface = TreeInterfaceDownstream(self, self.inbound_interface_index, self._rpc, non_root_upstream_state, non_root_interest_state, self.is_tree_active())
                self.interface_state[self.inbound_interface_index] = new_downstream_interface
                new_upstream_interface = TreeInterfaceUpstream(self, new_inbound_interface_index, root_upstream_state, True)
                self.interface_state[new_inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = new_inbound_interface_index

                # remove old interfaces
                old_upstream_interface.delete()
                old_downstream_interface.delete()

                if self.is_tree_active() and not new_upstream_interface.is_S_directly_conn() and all(value is None for value in self._upstream_interface_state.values()):
                    self.change_tree_to_unknown_state()
                elif self.is_tree_active() and not new_upstream_interface.is_S_directly_conn() and root_upstream_state is None:
                    self.change_tree_to_inactive_state()
                elif self.is_tree_inactive() and (new_upstream_interface.is_S_directly_conn() or root_upstream_state is not None):
                    self.change_tree_to_active_state()

                # atualizar tabela de encaminhamento multicast
                #self._was_olist_null = False
                self.change()
                self.evaluate_in_tree_change()
                #new_upstream_interface.change_on_unicast_routing(interface_change=True)
            '''
            elif self.rpf_node != rpf_node:
                self.rpf_node = rpf_node
                self.interface_state[self.inbound_interface_index].change_on_unicast_routing()
            '''
            if self._rpc != new_rpc:
                self._rpc = new_rpc
                for interface in self.interface_state.values():
                    interface.notify_rpc_change(new_rpc)


    def neighbor_removal(self, if_index, other_neighbors_remain):
        self.interface_state[if_index].neighbor_removal(other_neighbors_remain)

    def is_in_tree(self):
        for interface in self.interface_state.values():
            if interface.is_forwarding():
                return True
        return False

    def evaluate_in_tree_change(self):
        with self._lock_test2:
            is_in_tree = self.is_in_tree()

            if self._was_in_tree != is_in_tree:
                if is_in_tree:
                    self.interface_state[self.inbound_interface_index].node_is_in_tree()
                else:
                    self.interface_state[self.inbound_interface_index].node_is_out_tree()

                self._was_in_tree = is_in_tree

    def get_source(self):
        return self.source_ip

    def get_group(self):
        return self.group_ip

    def change(self):
        with self._multicast_change:
            if self._tree_state == ActiveTree:
                Main.kernel.set_multicast_route(self)

    def remove_entry(self):
        Main.kernel.remove_multicast_route(self)

    def delete_state(self):
        for state in self.interface_state.values():
            #if flood_remove_tree:
            #    state.send_remove_tree()
            state.delete()

    '''
    def delete(self, flood_remove_tree=False):
        #with self.CHANGE_STATE_LOCK:
        for state in self.interface_state.values():
            #if flood_remove_tree:
            #    state.send_remove_tree()
            state.delete()

        #from threading import Thread
        #thread = Thread(target=Main.kernel.remove_multicast_route, args=(self))
        #thread.start()
        #thread.join()
    '''

    ######################################
    # Interface change
    #######################################
    def new_interface(self, index):
        with self.CHANGE_STATE_LOCK:
            self.interface_state[index] = TreeInterfaceDownstream(self, index, self._rpc)
            self.change()
            self.evaluate_in_tree_change()

    def remove_interface(self, index):
        with self.CHANGE_STATE_LOCK:
            #check if removed interface is root interface
            if self.inbound_interface_index == index:
                #self.delete()
                self.remove_entry()
            else:
                self.interface_state.pop(index).delete()
                self.change()
                self.evaluate_in_tree_change()
