import sys
import time
import hashlib
import logging
import netifaces
import logging.handlers
from prettytable import PrettyTable
from hpimdm.TestLogger import RootFilter

from hpimdm.tree import hpim_globals
from hpimdm import UnicastRouting

interfaces = {}  # interfaces with multicast routing protocol enabled
interfaces_v6 = {}  # hpim ipv6 interfaces
igmp_interfaces = {}  # igmp interfaces
mld_interfaces = {}  # mld interfaces
kernel = None
kernel_v6 = None
unicast_routing = None
logger = None


def add_hpim_interface(interface_name, ipv4=True, ipv6=False):
    """
    Add a new interface to be controlled by HPIM-DM
    """
    if interface_name == "*":
        for interface_name in netifaces.interfaces():
            add_hpim_interface(interface_name, ipv4, ipv6)
        return

    if ipv4 and kernel is not None:
        kernel.create_hpim_interface(interface_name=interface_name)
    if ipv6 and kernel_v6 is not None:
        kernel_v6.create_hpim_interface(interface_name=interface_name)


def add_membership_interface(interface_name, ipv4=True, ipv6=False):
    """
    Add a new interface to be controlled by IGMP/MLD
    """
    if interface_name == "*":
        for interface_name in netifaces.interfaces():
            add_membership_interface(interface_name, ipv4, ipv6)
        return

    if ipv4 and kernel is not None:
        kernel.create_membership_interface(interface_name=interface_name)
    if ipv6 and kernel_v6 is not None:
        kernel_v6.create_membership_interface(interface_name=interface_name)


def remove_interface(interface_name, hpim=False, membership=False, ipv4=True, ipv6=False):
    """
    Remove HPIM-DM/IGMP interface
    """
    if interface_name == "*":
        for interface_name in netifaces.interfaces():
            remove_interface(interface_name, hpim, membership, ipv4, ipv6)
        return

    if ipv4 and kernel is not None:
        kernel.remove_interface(interface_name, hpim=hpim, membership=membership)
    if ipv6 and kernel_v6 is not None:
        kernel_v6.remove_interface(interface_name, hpim=hpim, membership=membership)


def list_neighbors(ipv4=False, ipv6=False):
    """
    List all neighbors in a human readable format
    """
    if ipv4:
        interfaces_list = interfaces.values()
    elif ipv6:
        interfaces_list = interfaces_v6.values()
    else:
        return "Unknown IP family"

    t = PrettyTable(['Interface', 'Neighbor IP', 'State', 'Hello Hold Time', 'BootTime', 'NeighborSnapshotSN', 'Uptime'])
    check_time = time.time()
    for interface in interfaces_list:
        for neighbor in interface.get_neighbors():
            uptime = check_time - neighbor.time_of_last_update
            uptime = 0 if (uptime < 0) else uptime

            t.add_row(
                [interface.interface_name, neighbor.ip, neighbor.neighbor_state.__name__, neighbor.hello_hold_time,
                 neighbor.time_of_boot, neighbor.neighbor_snapshot_sn, time.strftime("%H:%M:%S", time.gmtime(uptime))])
    print(t)
    return str(t)


def list_enabled_interfaces(ipv4=False, ipv6=False):
    """
    List all interfaces of the machine (enabled and not enabled for HPIM-DM and IGMP)
    """
    if ipv4:
        t = PrettyTable(['Interface', 'IP', 'HPIM/IGMP Enabled', 'HPIM security', 'IGMP State'])
        family = netifaces.AF_INET
        hpim_interfaces = interfaces
        membership_interfaces = igmp_interfaces
    elif ipv6:
        t = PrettyTable(['Interface', 'IP', 'HPIM/MLD Enabled', 'HPIM security', 'MLD State'])
        family = netifaces.AF_INET6
        hpim_interfaces = interfaces_v6
        membership_interfaces = mld_interfaces
    else:
        return "Unknown IP family"

    for interface in netifaces.interfaces():
        try:
            # TODO: fix same interface with multiple ips
            ip = netifaces.ifaddresses(interface)[family][0]['addr']
            hpim_enabled = interface in hpim_interfaces
            membership_enabled = interface in membership_interfaces
            enabled = str(hpim_enabled) + "/" + str(membership_enabled)
            hpim_protection = "-"
            if hpim_enabled and hpim_interfaces[interface].is_security_enabled():
                hpim_protection = str(hpim_interfaces[interface].security_id) + ": " + \
                                  hpim_interfaces[interface].hash_function.__name__
            membership_state = "-"
            if membership_enabled:
                membership_state = membership_interfaces[interface].interface_state.print_state()
            t.add_row([interface, ip, enabled, hpim_protection, membership_state])
        except Exception:
            continue
    print(t)
    return str(t)


def list_state(ipv4=True, ipv6=False):
    """
    List IGMP and HPIM-DM state
    For IGMP/MLD list the state of each group, regarding each interface
    For HPIM-DM list all trees and state of each interface
    """
    state_text = ""
    if ipv4:
        state_text = "IGMP State:\n{}\n\n\n\nMulticast Routing State:\n{}"
    elif ipv6:
        state_text = "MLD State:\n{}\n\n\n\nMulticast Routing State:\n{}"
    else:
        return state_text

    return state_text.format(list_membership_state(ipv4, ipv6), list_routing_state(ipv4, ipv6))


def list_membership_state(ipv4=True, ipv6=False):
    """
    List IGMP/MLD state (state of each group regarding each interface)
    """
    t = PrettyTable(['Interface', 'RouterState', 'Group Adress', 'GroupState'])
    if ipv4 and igmp_interfaces is not None:
        membership_interfaces = igmp_interfaces
    elif ipv6 and mld_interfaces is not None:
        membership_interfaces = mld_interfaces
    else:
        membership_interfaces = {}

    for (interface_name, interface_obj) in list(membership_interfaces.items()):
        interface_state = interface_obj.interface_state
        state_txt = interface_state.print_state()
        print(interface_state.group_state.items())

        for (group_addr, group_state) in list(interface_state.group_state.items()):
            print(group_addr)
            group_state_txt = group_state.print_state()
            t.add_row([interface_name, state_txt, group_addr, group_state_txt])
    return str(t)


def list_routing_state(ipv4=False, ipv6=False):
    """
    List HPIM-DM state (all state machines of each tree, regarding each interface)
    """
    if ipv4 and kernel is not None:
        routes = kernel.routing.values()
        vif_indexes = kernel.vif_index_to_name_dic.keys()
        dict_index_to_name = kernel.vif_index_to_name_dic
    elif ipv6 and kernel_v6 is not None:
        routes = kernel_v6.routing.values()
        vif_indexes = kernel_v6.vif_index_to_name_dic.keys()
        dict_index_to_name = kernel_v6.vif_index_to_name_dic
    else:
        routes = []
        vif_indexes = []
        dict_index_to_name = {}

    routing_entries = []
    for a in list(routes):
        for b in list(a.values()):
            routing_entries.append(b)

    t = PrettyTable(['SourceIP', 'GroupIP', 'TreeState', 'Interface', 'InterestState', 'AssertState', 'LocalMembership', "Is Forwarding?"])
    for entry in routing_entries:
        ip = entry.source_ip
        group = entry.group_ip
        upstream_if_index = entry.inbound_interface_index
        tree_state = str(entry._tree_state)

        for index in vif_indexes:
            interface_state = entry.interface_state[index]
            interface_name = dict_index_to_name[index]
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


def list_sequence_numbers(ipv4=False, ipv6=False):
    """
    List all stored sequence numbers
    """
    if ipv4 and interfaces is not None:
        hpim_interfaces = interfaces
    elif ipv6 and interfaces_v6 is not None:
        hpim_interfaces = interfaces_v6
    else:
        raise Exception("Unknown IP family")

    t = PrettyTable(['Interface', 'BootTime', 'InterfaceSN'])
    for (interface_name, interface_obj) in hpim_interfaces.copy().items():
        interface_boot_time = interface_obj.time_of_boot
        interface_sn = interface_obj.sequencer
        t.add_row([interface_name, interface_boot_time, interface_sn])
    table_txt = str(t) + "\n\n\n"

    t = PrettyTable(['Neighbor', 'BootTime', 'NeighborSnapshotSN', 'NeighborCheckpointSN'])
    for interface in hpim_interfaces.values():
        for neighbor in interface.get_neighbors():
            t.add_row([neighbor.ip, neighbor.time_of_boot, neighbor.neighbor_snapshot_sn, neighbor.checkpoint_sn])
    table_txt += str(t) + "\n\n"

    t = PrettyTable(['Neighbor', 'Tree', 'LastSN'])
    for interface in hpim_interfaces.values():
        for neighbor in interface.get_neighbors():
            neighbor_last_sn = neighbor.last_sequence_number.copy()
            for (tree, last_sn) in neighbor_last_sn.items():
                t.add_row([neighbor.ip, tree, last_sn])
    table_txt += str(t)
    return str(table_txt)


def list_neighbors_state(ipv4=False, ipv6=False):
    """
    List all stored state regarding each tree of each neighbor (Upstream and Interest state)
    """
    if ipv4 and interfaces is not None:
        hpim_interfaces = list(interfaces.values())
    elif ipv6 and interfaces_v6 is not None:
        hpim_interfaces = list(interfaces_v6.values())
    else:
        raise Exception("Unknown IP family")

    t = PrettyTable(['Interface', 'Neighbor', 'Tree', 'RPC Upstream State'])
    for interface in hpim_interfaces:
        for neighbor in interface.get_neighbors():
            for (tree_id, tree_state) in neighbor.tree_metric_state.copy().items():
                t.add_row([interface.interface_name, neighbor.ip, tree_id, tree_state])
    table_txt = "Upstream state:\n" + str(t)

    t = PrettyTable(['Interface', 'Neighbor', 'Tree', 'Interest State'])
    for interface in hpim_interfaces:
        for neighbor in interface.get_neighbors():
            for (tree_id, tree_state) in neighbor.tree_interest_state.copy().items():
                t.add_row([interface.interface_name, neighbor.ip, tree_id, tree_state])
    table_txt += "\n\n\nInterest state:\n" + str(t)
    return str(table_txt)


def list_hash_algorithms():
    """
    List compatible algorithms to be used on HMAC protection
    """
    t = PrettyTable(['HMAC Hash Algorithms'])
    for alg in hashlib.algorithms_guaranteed:
        t.add_row([alg])
    return str(t)


def add_security_key(interface_name, security_identifier, hash_function, key, ipv4=False, ipv6=False):
    """
    Enable HMAC protection in interface_name with security_identifier, HMAC based on hash_function and
    HMAC protection key
    """
    if ipv4 and kernel is not None:
        kernel.add_interface_security(interface_name, security_identifier, hash_function, key)
    elif ipv6 and kernel_v6 is not None:
        kernel_v6.add_interface_security(interface_name, security_identifier, hash_function, key)


def remove_security_key(interface_name, security_identifier, ipv4=False, ipv6=False):
    """
    Disable HMAC protection identified by security_identifier on interface interface_name
    """
    if ipv4 and kernel is not None:
        kernel.remove_interface_security(interface_name, security_identifier)
    elif ipv6 and kernel_v6 is not None:
        kernel_v6.remove_interface_security(interface_name, security_identifier)


def change_initial_flood_setting():
    """
    Change Initial Flood Setting, used to control the implicit interest of all neighbors
    (in order to flood or ignore initial packets)
    """
    hpim_globals.INITIAL_FLOOD_ENABLED ^= True
    if kernel is not None:
        kernel.recheck_all_trees_in_all_interfaces()
    if kernel_v6 is not None:
        kernel_v6.recheck_all_trees_in_all_interfaces()

    return "Flood is enabled?: " + str(hpim_globals.INITIAL_FLOOD_ENABLED)


def hold_forwarding_state():
    """
    Change Hold Forwarding State Setting, used to hold the forwarding state of an interface that was AW and that became
    AL
    """
    hpim_globals.AL_HOLD_FORWARDING_STATE_ENABLED ^= True
    return "Hold Forwarding State is enabled?: " + str(hpim_globals.AL_HOLD_FORWARDING_STATE_ENABLED)


def stop():
    """
    Stop process
    """
    remove_interface("*", hpim=True, membership=True, ipv4=True, ipv6=True)
    if kernel is not None:
        kernel.exit()
    if kernel_v6 is not None:
        kernel_v6.exit()
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


def enable_ipv6_kernel():
    """
    Function to explicitly enable IPv6 Multicast Routing stack.
    This may not be enabled by default due to some old linux kernels that may not have IPv6 stack or do not have
    IPv6 multicast routing support
    """
    global kernel_v6
    from hpimdm.Kernel import Kernel6
    kernel_v6 = Kernel6()

    global interfaces_v6
    global mld_interfaces
    interfaces_v6 = kernel_v6.hpim_interface
    mld_interfaces = kernel_v6.membership_interface


def main():
    """
    Start process
    """
    # logging
    global logger
    logger = logging.getLogger('hpim')
    logger.setLevel(logging.DEBUG)
    logger.addHandler(logging.StreamHandler(sys.stdout))

    global kernel
    from hpimdm.Kernel import Kernel4
    kernel = Kernel4()

    global unicast_routing
    unicast_routing = UnicastRouting.UnicastRouting()

    global interfaces
    global igmp_interfaces
    interfaces = kernel.hpim_interface
    igmp_interfaces = kernel.membership_interface

    try:
        enable_ipv6_kernel()
    except:
        pass
