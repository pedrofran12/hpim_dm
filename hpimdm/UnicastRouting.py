import socket
import ipaddress
from threading import RLock
from socket import if_indextoname
from pyroute2 import IPDB, IPRoute
from .tree import hpim_globals


def get_unicast_info(ip_dst):
    return UnicastRouting.get_unicast_info(ip_dst)


class UnicastRouting(object):
    ipdb = None
    lock = RLock()

    def __init__(self):
        UnicastRouting.ipdb = IPDB()
        self._ipdb = UnicastRouting.ipdb
        self._ipdb.register_callback(UnicastRouting.unicast_changes, mode="post")

    @staticmethod
    def get_route(ip_dst: str):
        """
        Get route from the unicast routing table regarding the entry of IP ip_dst
        """
        ip_version = ipaddress.ip_address(ip_dst).version
        if ip_version == 4:
            family = socket.AF_INET
            full_mask = 32
        elif ip_version == 6:
            family = socket.AF_INET6
            full_mask = 128
        else:
            raise Exception("Unknown IP version")
        info = None
        with UnicastRouting.lock:
            ipdb = UnicastRouting.ipdb  # type:IPDB

            for mask_len in range(full_mask, 0, -1):
                dst_network = str(ipaddress.ip_interface(ip_dst + "/" + str(mask_len)).network)

                print(dst_network)
                if dst_network in ipdb.routes.tables[hpim_globals.UNICAST_TABLE_ID]:
                    print(info)
                    if ipdb.routes[{'dst': dst_network, 'family': family,
                                    'table': hpim_globals.UNICAST_TABLE_ID}]['ipdb_scope'] != 'gc':
                        info = ipdb.routes[{'dst': dst_network, 'family': family,
                                            'table': hpim_globals.UNICAST_TABLE_ID}]
                    break
                else:
                    continue
            if not info:
                print("0.0.0.0/0 or ::/0")
                if "default" in ipdb.routes.tables[hpim_globals.UNICAST_TABLE_ID]:
                    info = ipdb.routes[{'dst': 'default', 'family': family, 'table': hpim_globals.UNICAST_TABLE_ID}]
            print(info)
            return info

    @staticmethod
    def get_unicast_info(ip_dst):
        """
        Obtain unicast info regarding IP ip_dst, such as RPC, if it is directly connected and root interface index
        """
        metric_administrative_distance = 0xFFFFFFFF
        metric_cost = 0xFFFFFFFF
        is_directly_connected = False
        oif = None
        with UnicastRouting.lock:
            unicast_route = UnicastRouting.get_route(ip_dst)
            if unicast_route is not None:
                oif = unicast_route.get("oif")
                next_hop = unicast_route["gateway"]
                multipaths = unicast_route["multipath"]
                #prefsrc = unicast_route.get("prefsrc")

                #rpf_node = ip_dst if (next_hop is None and prefsrc is not None) else next_hop
                rpf_node = next_hop if next_hop is not None else ip_dst
                if ipaddress.ip_address(ip_dst).version == 4:
                    highest_ip = ipaddress.ip_address("0.0.0.0")
                else:
                    highest_ip = ipaddress.ip_address("::")
                for m in multipaths:
                    if m.get("gateway", None) is None:
                        oif = m.get('oif')
                        rpf_node = ip_dst
                        break
                    elif ipaddress.ip_address(m["gateway"]) > highest_ip:
                        highest_ip = ipaddress.ip_address(m["gateway"])
                        oif = m.get('oif')
                        rpf_node = m["gateway"]

                metric_administrative_distance = unicast_route["proto"]
                metric_cost = unicast_route["priority"]
                metric_cost = metric_cost if metric_cost is not None else 0
                is_directly_connected = rpf_node == ip_dst

        interface_name = None if oif is None else if_indextoname(int(oif))
        from hpimdm import Main
        if ipaddress.ip_address(ip_dst).version == 4:
            rpf_if = Main.kernel.vif_name_to_index_dic.get(interface_name)
        else:
            rpf_if = Main.kernel_v6.vif_name_to_index_dic.get(interface_name)
        return (metric_administrative_distance, metric_cost, is_directly_connected, rpf_if)

    @staticmethod
    def unicast_changes(ipdb, msg, action):
        """
        Kernel notified about a change
        Verify the type of change and recheck all trees if necessary
        """
        print("unicast change?")
        print(action)
        UnicastRouting.lock.acquire()
        family = msg['family']
        if action == "RTM_NEWROUTE" or action == "RTM_DELROUTE":
            print(ipdb.routes)
            mask_len = msg["dst_len"]
            network_address = None
            attrs = msg["attrs"]
            print(attrs)
            for (key, value) in attrs:
                print((key, value))
                if key == "RTA_DST":
                    network_address = value
                    break
            if network_address is None and family == socket.AF_INET:
                network_address = "0.0.0.0"
            elif network_address is None and family == socket.AF_INET6:
                network_address = "::"
            print(network_address)
            print(mask_len)
            print(network_address + "/" + str(mask_len))
            subnet = ipaddress.ip_network(network_address + "/" + str(mask_len))
            print(str(subnet))
            UnicastRouting.lock.release()
            from hpimdm import Main
            if family == socket.AF_INET:
                Main.kernel.notify_unicast_changes(subnet)
            elif family == socket.AF_INET6:
                Main.kernel_v6.notify_unicast_changes(subnet)
            '''
        elif action == "RTM_NEWADDR" or action == "RTM_DELADDR":
            print(action)
            print(msg)
            interface_name = None
            attrs = msg["attrs"]
            for (key, value) in attrs:
                print((key, value))
                if key == "IFA_LABEL":
                    interface_name = value
                    break
            UnicastRouting.lock.release()
            try:
                Main.kernel.notify_interface_changes(interface_name)
            except:
                import traceback
                traceback.print_exc()
                pass
            subnet = ipaddress.ip_network("0.0.0.0/0")
            Main.kernel.notify_unicast_changes(subnet)
        elif action == "RTM_NEWLINK" or action == "RTM_DELLINK":
            attrs = msg["attrs"]
            if_name = None
            operation = None
            for (key, value) in attrs:
                print((key, value))
                if key == "IFLA_IFNAME":
                    if_name = value
                elif key == "IFLA_OPERSTATE":
                    operation = value
                if if_name is not None and operation is not None:
                    break
            if if_name is not None:
                print(if_name + ": " + operation)
            UnicastRouting.lock.release()
            if operation == 'DOWN':
                Main.kernel.remove_interface(if_name, igmp=True, pim=True)
            subnet = ipaddress.ip_network("0.0.0.0/0")
            Main.kernel.notify_unicast_changes(subnet)
            '''
        else:
            UnicastRouting.lock.release()

    def stop(self):
        """
        No longer monitor unicast changes....
        Invoked whenever the protocol is stopped
        """
        if self._ipdb:
            self._ipdb.release()
        if UnicastRouting.ipdb:
            UnicastRouting.ipdb = None
