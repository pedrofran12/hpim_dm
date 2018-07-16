import netifaces
import time
from prettytable import PrettyTable
import sys
import logging, logging.handlers
from TestLogger import RootFilter

from tree import globals
from Kernel import Kernel
import UnicastRouting

interfaces = {}  # interfaces with multicast routing protocol enabled
igmp_interfaces = {}  # igmp interfaces
kernel = None
unicast_routing = None
logger = None


def add_protocol_interface(interface_name):
    kernel.create_protocol_interface(interface_name=interface_name)


def add_igmp_interface(interface_name):
    kernel.create_igmp_interface(interface_name=interface_name)


def remove_interface(interface_name, pim=False, igmp=False):
    kernel.remove_interface(interface_name, pim=pim, igmp=igmp)


def list_neighbors():
    interfaces_list = interfaces.values()
    t = PrettyTable(['Interface', 'Neighbor IP', 'State', 'Hello Hold Time', "BootTime", "NeighborSnapshotSN", "Uptime"])
    check_time = time.time()
    for interface in interfaces_list:
        for neighbor in interface.get_neighbors():
            uptime = check_time - neighbor.time_of_last_update
            uptime = 0 if (uptime < 0) else uptime

            t.add_row(
                [interface.interface_name, neighbor.ip, neighbor.neighbor_state.__name__, neighbor.hello_hold_time, neighbor.time_of_boot, neighbor.neighbor_snapshot_sn, time.strftime("%H:%M:%S", time.gmtime(uptime))])
    print(t)
    return str(t)


def list_enabled_interfaces():
    global interfaces

    t = PrettyTable(['Interface', 'IP', 'Protocol/IGMP Enabled', 'IGMP State'])
    for interface in netifaces.interfaces():
        try:
            # TODO: fix same interface with multiple ips
            ip = netifaces.ifaddresses(interface)[netifaces.AF_INET][0]['addr']
            pim_enabled = interface in interfaces
            igmp_enabled = interface in igmp_interfaces
            enabled = str(pim_enabled) + "/" + str(igmp_enabled)
            if igmp_enabled:
                state = igmp_interfaces[interface].interface_state.print_state()
            else:
                state = "-"
            t.add_row([interface, ip, enabled, state])
        except Exception:
            continue
    print(t)
    return str(t)


def list_state():
    state_text = "IGMP State:\n" + list_igmp_state() + "\n\n\n\n" + "Multicast Routing State:\n" + list_routing_state()
    return state_text


def list_igmp_state():
    t = PrettyTable(['Interface', 'RouterState', 'Group Adress', 'GroupState'])
    for (interface_name, interface_obj) in list(igmp_interfaces.items()):
        interface_state = interface_obj.interface_state
        state_txt = interface_state.print_state()
        print(interface_state.group_state.items())

        for (group_addr, group_state) in list(interface_state.group_state.items()):
            print(group_addr)
            group_state_txt = group_state.print_state()
            t.add_row([interface_name, state_txt, group_addr, group_state_txt])
    return str(t)


def list_sequence_numbers():
    t = PrettyTable(['Interface', 'BootTime', 'InterfaceSN'])
    for (interface_name, interface_obj) in interfaces.copy().items():
        interface_boot_time = interface_obj.time_of_boot
        interface_sn = interface_obj.sequencer
        t.add_row([interface_name, interface_boot_time, interface_sn])
    table_txt = str(t) + "\n\n\n"

    t = PrettyTable(['Neighbor', 'BootTime', 'NeighborSnapshotSN', 'NeighborCheckpointSN'])
    for interface in interfaces.values():
        for neighbor in interface.get_neighbors():
            t.add_row([neighbor.ip, neighbor.time_of_boot, neighbor.neighbor_snapshot_sn, neighbor.checkpoint_sn])
    table_txt += str(t) + "\n\n"

    t = PrettyTable(['Neighbor', 'Tree', 'LastSN'])
    for interface in interfaces.values():
        for neighbor in interface.get_neighbors():
            neighbor_last_sn = neighbor.last_sequence_number.copy()
            for (tree, last_sn) in neighbor_last_sn.items():
                t.add_row([neighbor.ip, tree, last_sn])
    table_txt += str(t)
    return str(table_txt)


def list_neighbors_state():
    interfaces_list = interfaces.values()
    t = PrettyTable(['Interface', 'Neighbor', 'Tree', 'RPC Upstream State'])
    for interface in interfaces_list:
        for neighbor in interface.get_neighbors():
            for (tree_id, tree_state) in neighbor.tree_metric_state.copy().items():
                t.add_row([interface.interface_name, neighbor.ip, tree_id, tree_state])
    table_txt = "Upstream state:\n" + str(t)

    t = PrettyTable(['Interface', 'Neighbor', 'Tree', 'Interest State'])
    for interface in interfaces_list:
        for neighbor in interface.get_neighbors():
            for (tree_id, tree_state) in neighbor.tree_state.copy().items():
                t.add_row([interface.interface_name, neighbor.ip, tree_id, tree_state])
    table_txt += "\n\n\nInterest state:\n" + str(t)
    return str(table_txt)


def list_routing_state():
    routing_entries = []
    for a in list(kernel.routing.values()):
        for b in list(a.values()):
            routing_entries.append(b)
    vif_indexes = kernel.vif_index_to_name_dic.keys()

    t = PrettyTable(['SourceIP', 'GroupIP', 'TreeState', 'Interface', 'PruneState', 'AssertState', 'LocalMembership', "Is Forwarding?"])
    for entry in routing_entries:
        ip = entry.source_ip
        group = entry.group_ip
        upstream_if_index = entry.inbound_interface_index
        tree_state = entry._tree_state.__name__

        for index in vif_indexes:
            interface_state = entry.interface_state[index]
            interface_name = kernel.vif_index_to_name_dic[index]
            local_membership = type(interface_state._local_membership_state).__name__
            try:
                if index != upstream_if_index:
                    assert_state = type(interface_state._assert_state).__name__
                    prune_state = type(interface_state._downstream_node_interest_state).__name__
                    is_forwarding = interface_state.is_forwarding()
                else:
                    assert_state = "--"
                    prune_state = "--"
                    is_forwarding = "upstream"
            except:
                prune_state = "-"
                assert_state = "-"
                is_forwarding = "-"

            t.add_row([ip, group, tree_state, interface_name, prune_state, assert_state, local_membership, is_forwarding])
    return str(t)


def change_initial_flood_setting():
    globals.INITIAL_FLOOD_ENABLED ^= True
    kernel.recheck_all_trees_in_all_interfaces()
    return "Flood is enabled?: " + str(globals.INITIAL_FLOOD_ENABLED)


def stop():
    remove_interface("*", pim=True, igmp=True)
    kernel.exit()
    unicast_routing.stop()


def test(router_name, server_logger_ip):
    global logger
    socketHandler = logging.handlers.SocketHandler(server_logger_ip,
                                                   logging.handlers.DEFAULT_TCP_LOGGING_PORT)
    # don't bother with a formatter, since a socket handler sends the event as
    # an unformatted pickle
    socketHandler.addFilter(RootFilter(router_name))
    logger.addHandler(socketHandler)


def main():
    # logging
    global logger
    logger = logging.getLogger('protocol')
    logger.setLevel(logging.DEBUG)
    logger.addHandler(logging.StreamHandler(sys.stdout))

    global kernel
    kernel = Kernel()

    global unicast_routing
    unicast_routing = UnicastRouting.UnicastRouting()

    global interfaces
    global igmp_interfaces
    interfaces = kernel.protocol_interface
    igmp_interfaces = kernel.igmp_interface
