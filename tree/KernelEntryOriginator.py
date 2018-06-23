from tree.tree_if_upstream_originator import TreeInterfaceUpstream
from tree.tree_if_downstream import TreeInterfaceDownstream
from .tree_interface import TreeInterface
from threading import Timer, Lock, RLock
from tree.metric import AssertMetric, Metric
import UnicastRouting
from time import time
import Main
import logging
from . import globals
class TreeState:
    @staticmethod
    def transition_to_active(kernel_entry):
        if kernel_entry._tree_state == ActiveTree:
            return
        kernel_entry._tree_state = ActiveTree
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_active()
        kernel_entry.change()

    @staticmethod
    def transition_to_inactive(kernel_entry):
        if kernel_entry._tree_state == InactiveTree:
            return
        kernel_entry._tree_state = InactiveTree
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_inactive_or_unknown()
        kernel_entry.change()

    @staticmethod
    def transition_to_unknown(kernel_entry):
        if kernel_entry._tree_state == UnknownTree:
            return
        kernel_entry._tree_state = UnknownTree
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_inactive_or_unknown()
        kernel_entry.remove_entry()


class ActiveTree(TreeState):
    def __str__(self):
        return


class InactiveTree(TreeState):
    def __str__(self):
        return


class UnknownTree(TreeState):
    def __str__(self):
        return


class KernelEntryOriginator:
    KERNEL_LOGGER = logging.getLogger('protocol.KernelEntryOriginator')

    def __init__(self, source_ip: str, group_ip: str, upstream_state_dic=None, interest_state_dic=None):
        self.kernel_entry_logger = logging.LoggerAdapter(KernelEntryOriginator.KERNEL_LOGGER, {'tree': '(' + source_ip + ',' + group_ip + ')'})
        self.kernel_entry_logger.debug('Create KernelEntryOriginator')

        self.source_ip = source_ip
        self.group_ip = group_ip

        self.sat_is_running = True
        self._tree_state = ActiveTree

        if upstream_state_dic is None:
            upstream_state_dic = {}
        if interest_state_dic is None:
            interest_state_dic = {}

        self._interest_interface_state = interest_state_dic
        self._upstream_interface_state = upstream_state_dic
        # ip of neighbor of the rpf
        #next_hop = UnicastRouting.get_route(source_ip)["gateway"]
        #self.rpf_node = source_ip if next_hop is None else next_hop


        # CHECK UNICAST ROUTING INFORMATION###################################################
        # CHOSE RPC INTERFACE
        # GET RPC TO SOURCE
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
        ######################################################################################

        # Locks
        self._multicast_change = Lock()
        self._lock_test2 = RLock()
        self.CHANGE_STATE_LOCK = RLock()

        # decide inbound interface based on rpf check
        #with Main.kernel.interface_lock:
        self.inbound_interface_index = Main.kernel.vif_dic[self.check_rpf()]

        self.interface_state = {}  # type: Dict[int, TreeInterface]
        tree_is_active = True
        with self.CHANGE_STATE_LOCK:
            for i in Main.kernel.vif_index_to_name_dic.keys():
                try:
                    upstream_state = self._upstream_interface_state.get(i, None)

                    if i != self.inbound_interface_index:
                        interest_state = self._interest_interface_state.get(i, True) # TODO CORRIGIR!!!
                        self.interface_state[i] = TreeInterfaceDownstream(self, i, self._rpc,
                                                                          best_upstream_router=upstream_state,
                                                                          interest_state=interest_state,
                                                                          tree_is_active=tree_is_active)
                except:
                    import traceback
                    print(traceback.print_exc())
                    continue


            self.interface_state[self.inbound_interface_index] = TreeInterfaceUpstream(self, self.inbound_interface_index,
                                                                                       None)

        self.change()
        self.check_tree_state()
        print('Tree created')


    def is_S_directly_conn(self):
        return self.rpf_node == self.source_ip

    def get_inbound_interface_index(self):
        return self.inbound_interface_index

    def get_outbound_interfaces_indexes(self):
        '''
        outbound_indexes = [0] * Main.kernel.MAXVIFS
        if self.is_tree_active():
            for (index, state) in self.interface_state.items():
                outbound_indexes[index] = state.is_forwarding()
        else:
            outbound_indexes = [1] * Main.kernel.MAXVIFS
        '''
        outbound_indexes = [0] * Main.kernel.MAXVIFS
        for (index, state) in self.interface_state.items():
            outbound_indexes[index] = state.is_forwarding()
        return outbound_indexes

    def check_rpf(self):
        return UnicastRouting.check_rpf(self.source_ip)


    def check_tree_state(self):
        if self.sat_is_running:
            print("PARA ACTIVE")
            self._tree_state.transition_to_active(self)
        elif not self.sat_is_running and all(value is None for value in self._upstream_interface_state.values()):
            # tree is unknown
            print("PARA UNKNOWN")
            self._tree_state.transition_to_unknown(self)
        elif not self.sat_is_running:
            print("PARA INACTIVE")
            self._tree_state.transition_to_inactive(self)


    ################################################
    # Receive (S,G) data packets or control packets
    ################################################
    def recv_data_msg(self, index):
        print("recv data")
        self.interface_state[index].recv_data_msg()

    '''
    def recv_ack_msg(self, index, packet):
        print("recv ack msg")
        sender_ip = packet.ip_header.ip_src
        pkt_ack = packet.payload.payload
        acked_sequence_number = pkt_ack.sequence_number
        self.interface_state[index].recv_ack_msg(sender_ip, acked_sequence_number)

    def recv_ack_sync_msg(self, index, neighbor_ip, minimum_sn):
        print("recv ack sync msg")
        self.interface_state[index].recv_ack_sync_msg(neighbor_ip, minimum_sn)
    '''

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
    def sat_expires(self):
        self.sat_is_running = False
        self.check_tree_state()

    def sat_running(self):
        self.sat_is_running = True
        self.check_tree_state()

    def check_interface_state(self, index, upstream_state, interest_state):
        print("ENTROU CHECK INTERFACE STATE")
        if index == self.inbound_interface_index:
            return

        self._upstream_interface_state[index] = upstream_state

        self.interface_state[index].change_assert_state(upstream_state)
        self.check_interest_state(index, interest_state)

        self.check_tree_state()
        print("SAI CHECK INTERFACE STATE")

    def check_interest_state(self, index, interest_state):
        if index == self.inbound_interface_index:
            return

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

    '''
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
            if index in self.interface_state:
                self._inactive_interfaces_that_are_ready[index] = True

            print("INTERFACES NOT READY??: ", False in self._inactive_interfaces_that_are_ready.values())
            if False in self._inactive_interfaces_that_are_ready.values():
                return

        #self.delete()
            if self.is_tree_unknown():
                self.remove_entry()
    '''

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
                new_downstream_interface = TreeInterfaceDownstream(self, self.inbound_interface_index, self._rpc, non_root_upstream_state, non_root_interest_state, self.is_tree_active(), was_root=True)
                self.interface_state[self.inbound_interface_index] = new_downstream_interface
                new_upstream_interface = TreeInterfaceUpstream(self, new_inbound_interface_index, root_upstream_state)
                self.interface_state[new_inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = new_inbound_interface_index

                # remove old interfaces
                old_upstream_interface.delete()
                old_downstream_interface.delete()

                self.check_tree_state()

                # atualizar tabela de encaminhamento multicast
                #self._was_olist_null = False
                self.change()
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

    '''
    def neighbor_removal(self, if_index, other_neighbors_remain):
        self.interface_state[if_index].neighbor_removal(other_neighbors_remain)
    '''

    def is_in_tree(self):
        for interface in self.interface_state.values():
            if interface.is_forwarding():
                return True
        return False

    def evaluate_in_tree_change(self):
        return


    def get_source(self):
        return self.source_ip

    def get_group(self):
        return self.group_ip

    def change(self):
        with self._multicast_change:
            if self._tree_state != UnknownTree:
                Main.kernel.set_multicast_route(self)

    def stop_flood(self):
        self.still_flooding = False
        self.change()

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
        print("NEW_INTERFACE ANTES")
        with self.CHANGE_STATE_LOCK:
            print("NEW_INTERFACE DEPOIS")
            if index in self.interface_state:
                return

            interest_state = False
            interface_name = Main.kernel.vif_index_to_name_dic.get(index, None)
            if interface_name in Main.kernel.protocol_interface:
                (interest_state, upstream_state) = Main.kernel.protocol_interface.get(interface_name).get_tree_state(
                    (self.source_ip, self.group_ip))

            self._interest_interface_state[index] = interest_state
            self._upstream_interface_state[index] = None
            self._inactive_interfaces_that_are_ready[index] = False

            self.interface_state[index] = TreeInterfaceDownstream(self, index, self._rpc, tree_is_active=self.is_tree_active(), interest_state=interest_state)

            self.change()
            self.evaluate_in_tree_change()

    def remove_interface(self, index):
        with self.CHANGE_STATE_LOCK:
            #check if removed interface is root interface
            if self.inbound_interface_index == index:
                #self.delete()
                self.remove_entry()
            elif index in self.interface_state:
                self.interface_state.pop(index).delete()

                # remove cached info about removed interface
                self._upstream_interface_state.pop(index)
                self._interest_interface_state.pop(index)
                self._inactive_interfaces_that_are_ready.pop(index)

                self.change()
                self.evaluate_in_tree_change()

                # if tree is being removed, notify that this interface is ready
                self.notify_interface_is_ready_to_remove(index)
