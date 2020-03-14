import sys
import time
import hashlib
import logging
import logging.handlers
from prettytable import PrettyTable
import netifaces
from hpimdm.TestLogger import RootFilter

from hpimdm.tree import protocol_globals
from hpimdm import UnicastRouting

interfaces = {}  # interfaces with multicast routing protocol enabled
igmp_interfaces = {}  # igmp interfaces
kernel = None
unicast_routing = None
logger = None


def add_protocol_interface(interface_name):
    """
    Add a new interface to be controlled by HPIM-DM
    """
    kernel.create_protocol_interface(interface_name=interface_name)


def add_igmp_interface(interface_name):
    """
    Add a new interface to be controlled by IGMP
    """
    kernel.create_igmp_interface(interface_name=interface_name)


def remove_interface(interface_name, pim=False, igmp=False):
    """
    Remove HPIM-DM/IGMP interface
    """
    kernel.remove_interface(interface_name, pim=pim, igmp=igmp)


def list_neighbors():
    """
    List all neighbors in a human readable format
    """
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
    """
    List all interfaces of the machine (enabled and not enabled for HPIM-DM and IGMP)
    """
    t = PrettyTable(['Interface', 'IP', 'HPIM/IGMP Enabled', 'HPIM security', 'IGMP State'])
    for interface in netifaces.interfaces():
        try:
            # TODO: fix same interface with multiple ips
            ip = netifaces.ifaddresses(interface)[netifaces.AF_INET][0]['addr']
            hpim_enabled = interface in interfaces
            igmp_enabled = interface in igmp_interfaces
            enabled = str(hpim_enabled) + "/" + str(igmp_enabled)
            hpim_protection = "-"
            if hpim_enabled and interfaces[interface].is_security_enabled():
                hpim_protection = str(interfaces[interface].security_id) + ": " + interfaces[interface].hash_function.__name__
            igmp_state = "-"
            if igmp_enabled:
                igmp_state = igmp_interfaces[interface].interface_state.print_state()
            t.add_row([interface, ip, enabled, hpim_protection, igmp_state])
        except Exception:
            continue
    print(t)
    return str(t)


def list_state():
    """
    List IGMP and HPIM-DM state
    For IGMP list the state of each group, regarding each interface
    For HPIM-DM list all trees and state of each interface
    """
    state_text = "IGMP State:\n" + list_igmp_state() + "\n\n\n\n" + "Multicast Routing State:\n" + list_routing_state()
    return state_text


def list_igmp_state():
    """
    List IGMP state (state of each group regarding each interface)
    """
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
    """
    List all stored sequence numbers
    """
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
    """
    List all stored state regarding each tree of each neighbor (Upstream and Interest state)
    """
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
            for (tree_id, tree_state) in neighbor.tree_interest_state.copy().items():
                t.add_row([interface.interface_name, neighbor.ip, tree_id, tree_state])
    table_txt += "\n\n\nInterest state:\n" + str(t)
    return str(table_txt)


def list_routing_state():
    """
    List HPIM-DM state (all state machines of each tree, regarding each interface)
    """
    routing_entries = []
    for a in list(kernel.routing.values()):
        for b in list(a.values()):
            routing_entries.append(b)
    vif_indexes = kernel.vif_index_to_name_dic.keys()

    t = PrettyTable(['SourceIP', 'GroupIP', 'TreeState', 'Interface', 'InterestState', 'AssertState', 'LocalMembership', "Is Forwarding?"])
    for entry in routing_entries:
        ip = entry.source_ip
        group = entry.group_ip
        upstream_if_index = entry.inbound_interface_index
        tree_state = str(entry._tree_state)

        for index in vif_indexes:
            interface_state = entry.interface_state[index]
            interface_name = kernel.vif_index_to_name_dic[index]
            local_membership = str(interface_state._local_membership_state)
            try:
                if index != upstream_if_index:
                    assert_state = str(interface_state._assert_state)
                    prune_state = str(interface_state._downstream_node_interest_state)
                    is_forwarding = interface_state.is_forwarding()
                else:
                    assert_state = "--"
                    prune_state = "--"
                    is_forwarding = "root"
            except:
                prune_state = "-"
                assert_state = "-"
                is_forwarding = "-"

            t.add_row([ip, group, tree_state, interface_name, prune_state, assert_state, local_membership, is_forwarding])
    return str(t)


def list_hash_algorithms():
    """
    List compatible algorithms to be used on HMAC protection
    """
    t = PrettyTable(['HMAC Hash Algorithms'])
    for alg in hashlib.algorithms_guaranteed:
        t.add_row([alg])
    return str(t)


def add_security_key(interface_name, security_identifier, hash_function, key):
    """
    Enable HMAC protection in interface_name with security_identifier, HMAC based on hash_function and
    HMAC protection key
    """
    kernel.add_interface_security(interface_name, security_identifier, hash_function, key)


def remove_security_key(interface_name, security_identifier):
    """
    Disable HMAC protection identified by security_identifier on interface interface_name
    """
    kernel.remove_interface_security(interface_name, security_identifier)


def change_initial_flood_setting():
    """
    Change Initial Flood Setting, used to control the implicit interest of all neighbors
    (in order to flood or ignore initial packets)
    """
    protocol_globals.INITIAL_FLOOD_ENABLED ^= True
    kernel.recheck_all_trees_in_all_interfaces()
    return "Flood is enabled?: " + str(protocol_globals.INITIAL_FLOOD_ENABLED)


def hold_forwarding_state():
    """
    Change Hold Forwarding State Setting, used to hold the forwarding state of an interface that was AW and that became
    AL
    """
    protocol_globals.AL_HOLD_FORWARDING_STATE_ENABLED ^= True
    return "Hold Forwarding State is enabled?: " + str(protocol_globals.AL_HOLD_FORWARDING_STATE_ENABLED)


def stop():
    """
    Stop process
    """
    remove_interface("*", pim=True, igmp=True)
    kernel.exit()
    unicast_routing.stop()


def test(router_name, server_logger_ip):
    """
    Test setting.... Used to send logs to a remote server
    """
    global logger
    socketHandler = logging.handlers.SocketHandler(server_logger_ip,
                                                   logging.handlers.DEFAULT_TCP_LOGGING_PORT)
    # don't bother with a formatter, since a socket handler sends the event as
    # an unformatted pickle
    socketHandler.addFilter(RootFilter(router_name))
    logger.addHandler(socketHandler)


def main():
    """
    Start process
    """
    # logging
    global logger
    logger = logging.getLogger('protocol')
    logger.setLevel(logging.DEBUG)
    logger.addHandler(logging.StreamHandler(sys.stdout))

    global kernel
    from hpimdm.Kernel import Kernel
    kernel = Kernel()

    global unicast_routing
    unicast_routing = UnicastRouting.UnicastRouting()

    global interfaces
    global igmp_interfaces
    interfaces = kernel.protocol_interface
    igmp_interfaces = kernel.igmp_interface
