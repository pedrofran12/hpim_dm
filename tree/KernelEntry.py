from tree.tree_if_upstream import TreeInterfaceUpstream
from tree.tree_if_downstream import TreeInterfaceDownstream
from .tree_interface import TreeInterface
from threading import Timer, Lock, RLock
from tree.metric import AssertMetric, Metric
import UnicastRouting
from time import time
import Main
import logging

class KernelEntry:
    KERNEL_LOGGER = logging.getLogger('protocol.KernelEntry')

    def __init__(self, source_ip: str, group_ip: str):
        self.kernel_entry_logger = logging.LoggerAdapter(KernelEntry.KERNEL_LOGGER, {'tree': '(' + source_ip + ',' + group_ip + ')'})
        self.kernel_entry_logger.debug('Create KernelEntry')

        self.source_ip = source_ip
        self.group_ip = group_ip

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
                        self.interface_state[i] = TreeInterfaceUpstream(self, i)
                    else:
                        self.interface_state[i] = TreeInterfaceDownstream(self, i, self._rpc)
                except:
                    import traceback
                    print(traceback.print_exc())
                    continue

        self.change()
        self.evaluate_in_tree_change()
        print('Tree created')

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

    def recv_assert_msg(self, index, packet):
        print("recv assert")
        pkt_assert = packet.payload.payload
        metric = pkt_assert.metric
        metric_preference = pkt_assert.metric_preference
        assert_sender_ip = packet.ip_header.ip_src

        received_metric = AssertMetric(metric_preference=metric_preference, route_metric=metric, ip_address=assert_sender_ip)
        self.interface_state[index].recv_assert_msg(received_metric)

    def recv_tree_interest_query_msg(self, index, packet):
        print("recv tree_interest_query msg")
        self.interface_state[index].recv_tree_interest_query_msg()

    def recv_join_msg(self, index, packet):
        print("recv join msg")
        self.interface_state[index].recv_join_msg()

    ################################################
    # Send state refresh msg
    ################################################
    def forward_state_refresh_msg(self, state_refresh_packet):
        for interface in self.interface_state.values():
            interface.send_state_refresh(state_refresh_packet)


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
                self.delete()
                return
            if new_inbound_interface_index != self.inbound_interface_index:
                self.rpf_node = rpf_node

                # get old interfaces
                old_upstream_interface = self.interface_state[self.inbound_interface_index]
                old_downstream_interface = self.interface_state[new_inbound_interface_index]

                # change type of interfaces
                new_downstream_interface = TreeInterfaceDownstream(self, self.inbound_interface_index, self._rpc)
                self.interface_state[self.inbound_interface_index] = new_downstream_interface
                new_upstream_interface = TreeInterfaceUpstream(self, new_inbound_interface_index)
                self.interface_state[new_inbound_interface_index] = new_upstream_interface
                self.inbound_interface_index = new_inbound_interface_index

                # remove old interfaces
                old_upstream_interface.delete(change_type_interface=True)
                old_downstream_interface.delete(change_type_interface=True)

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
            Main.kernel.set_multicast_route(self)

    def delete(self, flood_remove_tree=False):
        with self._multicast_change:
            for state in self.interface_state.values():
                if flood_remove_tree:
                    state.send_remove_tree()
                state.delete()

            Main.kernel.remove_multicast_route(self)


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
                self.delete()
            else:
                self.interface_state.pop(index).delete()
                self.change()
                self.evaluate_in_tree_change()
