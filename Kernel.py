import socket
import struct
from threading import Lock, Thread
import traceback

import ipaddress

import netifaces
import UnicastRouting
'''
from Packet.PacketProtocolSetTree import PacketProtocolSetTree
from Packet.PacketProtocolRemoveTree import PacketProtocolRemoveTree
from Packet.PacketProtocolActiveTrees import PacketProtocolActiveTrees
from Packet.PacketProtocolConfirm import PacketProtocolConfirm
'''
from Packet.PacketProtocolHeader import PacketProtocolHeader

from RWLock.RWLock import RWLockWrite
import Main

from InterfaceProtocol import InterfaceProtocol
from InterfaceIGMP import InterfaceIGMP
from tree.KernelEntry import KernelEntry
from Packet.Packet import Packet


class Kernel:
    # MRT
    MRT_BASE    = 200
    MRT_INIT    = (MRT_BASE)      # /* Activate the kernel mroute code 	*/
    MRT_DONE    = (MRT_BASE + 1)  # /* Shutdown the kernel mroute		*/
    MRT_ADD_VIF = (MRT_BASE + 2)  # /* Add a virtual interface		    */
    MRT_DEL_VIF = (MRT_BASE + 3)  # /* Delete a virtual interface		*/
    MRT_ADD_MFC = (MRT_BASE + 4)  # /* Add a multicast forwarding entry	*/
    MRT_DEL_MFC = (MRT_BASE + 5)  # /* Delete a multicast forwarding entry	*/
    MRT_VERSION = (MRT_BASE + 6)  # /* Get the kernel multicast version	*/
    MRT_ASSERT  = (MRT_BASE + 7)  # /* Activate PIM assert mode		    */
    MRT_PIM     = (MRT_BASE + 8)  # /* enable PIM code			        */
    MRT_TABLE   = (MRT_BASE + 9)  # /* Specify mroute table ID		    */
    #MRT_ADD_MFC_PROXY = (MRT_BASE + 10)  # /* Add a (*,*|G) mfc entry	*/
    #MRT_DEL_MFC_PROXY = (MRT_BASE + 11)  # /* Del a (*,*|G) mfc entry	*/
    #MRT_MAX = (MRT_BASE + 11)


    # Max Number of Virtual Interfaces
    MAXVIFS = 32

    # SIGNAL MSG TYPE
    IGMPMSG_NOCACHE = 1
    IGMPMSG_WRONGVIF = 2
    IGMPMSG_WHOLEPKT = 3  # NOT USED ON PIM-DM


    # Interface flags
    VIFF_TUNNEL      = 0x1  # IPIP tunnel
    VIFF_SRCRT       = 0x2  # NI
    VIFF_REGISTER    = 0x4  # register vif
    VIFF_USE_IFINDEX = 0x8  # use vifc_lcl_ifindex instead of vifc_lcl_addr to find an interface

    def __init__(self):
        # Kernel is running
        self.running = True

        # KEY : interface_ip, VALUE : vif_index
        self.vif_dic = {}
        self.vif_index_to_name_dic = {}
        self.vif_name_to_index_dic = {}

        # KEY : source_ip, VALUE : {group_ip: KernelEntry}
        self.routing = {}

        s = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_IGMP)

        # MRT INIT
        s.setsockopt(socket.IPPROTO_IP, Kernel.MRT_INIT, 1)

        # MRT PIM
        s.setsockopt(socket.IPPROTO_IP, Kernel.MRT_PIM, 0)
        s.setsockopt(socket.IPPROTO_IP, Kernel.MRT_ASSERT, 0)

        self.socket = s
        self.rwlock = RWLockWrite()
        self.interface_lock = Lock()

        # Create register interface
        # todo useless in PIM-DM... useful in PIM-SM
        #self.create_virtual_interface("0.0.0.0", "pimreg", index=0, flags=Kernel.VIFF_REGISTER)


        self.protocol_interface = {} # name: interface_protocol
        self.igmp_interface = {}  # name: interface_igmp

        # logs
        self.interface_logger = Main.logger.getChild('KernelInterface')
        self.tree_logger = Main.logger.getChild('KernelTree')

        # receive signals from kernel with a background thread
        handler_thread = Thread(target=self.handler)
        handler_thread.daemon = True
        handler_thread.start()

    '''
    Structure to create/remove virtual interfaces
    struct vifctl {
        vifi_t	vifc_vifi;		        /* Index of VIF */
        unsigned char vifc_flags;	    /* VIFF_ flags */
        unsigned char vifc_threshold;	/* ttl limit */
        unsigned int vifc_rate_limit;	/* Rate limiter values (NI) */
        union {
            struct in_addr vifc_lcl_addr;     /* Local interface address */
            int            vifc_lcl_ifindex;  /* Local interface index   */
        };
        struct in_addr vifc_rmt_addr;	/* IPIP tunnel addr */
    };
    '''
    def create_virtual_interface(self, ip_interface: str or bytes, interface_name: str, index, flags=0x0):
        if type(ip_interface) is str:
            ip_interface = socket.inet_aton(ip_interface)

        struct_mrt_add_vif = struct.pack("HBBI 4s 4s", index, flags, 1, 0, ip_interface,
                                         socket.inet_aton("0.0.0.0"))
        self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_ADD_VIF, struct_mrt_add_vif)
        self.vif_dic[socket.inet_ntoa(ip_interface)] = index
        self.vif_index_to_name_dic[index] = interface_name
        self.vif_name_to_index_dic[interface_name] = index

        with self.rwlock.genWlock():
            for source_dict in list(self.routing.values()):
                for kernel_entry in list(source_dict.values()):
                    kernel_entry.new_interface(index)

        self.interface_logger.debug('Create virtual interface: %s -> %d', interface_name, index)
        return index


    def create_protocol_interface(self, interface_name: str):
        with self.interface_lock:
            protocol_interface = self.protocol_interface.get(interface_name)
            igmp_interface = self.igmp_interface.get(interface_name)
            vif_already_exists = protocol_interface or igmp_interface
            if protocol_interface:
                # already exists
                return
            elif igmp_interface:
                index = igmp_interface.vif_index
            else:
                index = list(range(0, self.MAXVIFS) - self.vif_index_to_name_dic.keys())[0]

            ip_interface = None
            if interface_name not in self.protocol_interface:
                pim_interface = InterfaceProtocol(interface_name, index)
                self.protocol_interface[interface_name] = pim_interface
                ip_interface = pim_interface.ip_interface

            if not vif_already_exists:
                self.create_virtual_interface(ip_interface=ip_interface, interface_name=interface_name, index=index)

    def create_igmp_interface(self, interface_name: str):
        with self.interface_lock:
            protocol_interface = self.protocol_interface.get(interface_name)
            igmp_interface = self.igmp_interface.get(interface_name)
            vif_already_exists = protocol_interface or igmp_interface
            if igmp_interface:
                # already exists
                return
            elif protocol_interface:
                index = protocol_interface.vif_index
            else:
                index = list(range(0, self.MAXVIFS) - self.vif_index_to_name_dic.keys())[0]

            ip_interface = None
            if interface_name not in self.igmp_interface:
                igmp_interface = InterfaceIGMP(interface_name, index)
                self.igmp_interface[interface_name] = igmp_interface
                ip_interface = igmp_interface.ip_interface

            if not vif_already_exists:
                self.create_virtual_interface(ip_interface=ip_interface, interface_name=interface_name, index=index)


    def remove_interface(self, interface_name, igmp:bool=False, pim:bool=False):
        with self.interface_lock:
            ip_interface = None
            pim_interface = self.protocol_interface.get(interface_name)
            igmp_interface = self.igmp_interface.get(interface_name)
            if (igmp and not igmp_interface) or (pim and not pim_interface) or (not igmp and not pim):
                return
            if pim:
                pim_interface = self.protocol_interface.pop(interface_name)
                ip_interface = pim_interface.ip_interface
                pim_interface.remove()
            elif igmp:
                igmp_interface = self.igmp_interface.pop(interface_name)
                ip_interface = igmp_interface.ip_interface
                igmp_interface.remove()

            if (not self.igmp_interface.get(interface_name) and not self.protocol_interface.get(interface_name)):
                self.remove_virtual_interface(ip_interface)


    def remove_virtual_interface(self, ip_interface):
        #with self.interface_lock:
        index = self.vif_dic[ip_interface]
        struct_vifctl = struct.pack("HBBI 4s 4s", index, 0, 0, 0, socket.inet_aton("0.0.0.0"), socket.inet_aton("0.0.0.0"))

        self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_DEL_VIF, struct_vifctl)

        del self.vif_dic[ip_interface]
        del self.vif_name_to_index_dic[self.vif_index_to_name_dic[index]]
        interface_name = self.vif_index_to_name_dic.pop(index)

        # alterar MFC's para colocar a 0 esta interface
        with self.rwlock.genWlock():
            for source_dict in list(self.routing.values()):
                for kernel_entry in list(source_dict.values()):
                    kernel_entry.remove_interface(index)

        self.interface_logger.debug('Remove virtual interface: %s -> %d', interface_name, index)



    '''
    /* Cache manipulation structures for mrouted and PIMd */
    struct mfcctl {
        struct in_addr mfcc_origin;		    /* Origin of mcast	*/
        struct in_addr mfcc_mcastgrp;		/* Group in question	*/
        vifi_t mfcc_parent; 			    /* Where it arrived	*/
        unsigned char mfcc_ttls[MAXVIFS];	/* Where it is going	*/
        unsigned int mfcc_pkt_cnt;		    /* pkt count for src-grp */
        unsigned int mfcc_byte_cnt;
        unsigned int mfcc_wrong_if;
        int mfcc_expire;
    };
    '''
    def set_multicast_route(self, kernel_entry: KernelEntry):
        source_ip = socket.inet_aton(kernel_entry.source_ip)
        group_ip = socket.inet_aton(kernel_entry.group_ip)

        outbound_interfaces = kernel_entry.get_outbound_interfaces_indexes()
        if len(outbound_interfaces) != Kernel.MAXVIFS:
            raise Exception

        #outbound_interfaces_and_other_parameters = list(kernel_entry.outbound_interfaces) + [0]*4
        outbound_interfaces_and_other_parameters = outbound_interfaces + [0]*4

        #outbound_interfaces, 0, 0, 0, 0 <- only works with python>=3.5
        #struct_mfcctl = struct.pack("4s 4s H " + "B"*Kernel.MAXVIFS + " IIIi", source_ip, group_ip, inbound_interface_index, *outbound_interfaces, 0, 0, 0, 0)
        struct_mfcctl = struct.pack("4s 4s H " + "B"*Kernel.MAXVIFS + " IIIi", source_ip, group_ip, kernel_entry.inbound_interface_index, *outbound_interfaces_and_other_parameters)
        self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_ADD_MFC, struct_mfcctl)


    def remove_multicast_route(self, kernel_entry: KernelEntry):
        Thread(target=self._remove_multicast_route, args=(kernel_entry,)).start()
        #self._remove_multicast_route(kernel_entry, struct_mfcctl)

    def _remove_multicast_route(self, kernel_entry):
        source_ip = socket.inet_aton(kernel_entry.source_ip)
        group_ip = socket.inet_aton(kernel_entry.group_ip)
        outbound_interfaces_and_other_parameters = [0] + [0]*Kernel.MAXVIFS + [0]*4

        struct_mfcctl = struct.pack("4s 4s H " + "B"*Kernel.MAXVIFS + " IIIi", source_ip, group_ip, *outbound_interfaces_and_other_parameters)
        with self.rwlock.genWlock():
            source_ip = kernel_entry.source_ip
            group_ip = kernel_entry.group_ip

            if not (source_ip in self.routing and group_ip in self.routing[source_ip]):
                return
            self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_DEL_MFC, struct_mfcctl)
            self.routing[kernel_entry.source_ip].pop(kernel_entry.group_ip)
            kernel_entry.delete_state()
            if len(self.routing[source_ip]) == 0:
                self.routing.pop(source_ip)


            for interface in self.protocol_interface.values():
                interest_state = False
                upstream_state = None
                for n in interface.neighbors.values():
                    (neighbor_interest_state, neighbor_upstream_state) = n.get_tree_state(tree=(source_ip, group_ip))
                    if not interest_state and neighbor_interest_state:
                        interest_state = neighbor_interest_state

                    if neighbor_upstream_state is not None:
                        if upstream_state is None:
                            upstream_state = neighbor_upstream_state
                        elif neighbor_upstream_state.is_better_than(upstream_state):
                            upstream_state = neighbor_upstream_state

                tree_is_active = upstream_state is not None
                if tree_is_active:
                    if source_ip in self.routing:
                        if group_ip in self.routing[source_ip]:
                            kernel_entry = self.routing[source_ip][group_ip]
                        else:
                            kernel_entry = KernelEntry(source_ip, group_ip)
                            self.routing[source_ip][group_ip] = kernel_entry
                    else:
                        kernel_entry = KernelEntry(source_ip, group_ip)
                        self.routing[source_ip] = {group_ip: kernel_entry}
                    kernel_entry.check_interface_state(interface.vif_index, upstream_state, interest_state)






    def exit(self):
        self.running = False

        # MRT DONE
        self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_DONE, 1)
        self.socket.close()


    '''
    /* This is the format the mroute daemon expects to see IGMP control
    * data. Magically happens to be like an IP packet as per the original
    */
    struct igmpmsg {
        __u32 unused1,unused2;
        unsigned char im_msgtype;		/* What is this */
        unsigned char im_mbz;			/* Must be zero */
        unsigned char im_vif;			/* Interface (this ought to be a vifi_t!) */
        unsigned char unused3;
        struct in_addr im_src,im_dst;
    };
    '''
    def handler(self):
        while self.running:
            try:
                msg = self.socket.recv(20)
                (_, _, im_msgtype, im_mbz, im_vif, _, im_src, im_dst) = struct.unpack("II B B B B 4s 4s", msg[:20])
                print((im_msgtype, im_mbz, socket.inet_ntoa(im_src), socket.inet_ntoa(im_dst)))

                if im_mbz != 0:
                    continue

                print(im_msgtype)
                print(im_mbz)
                print(im_vif)
                print(socket.inet_ntoa(im_src))
                print(socket.inet_ntoa(im_dst))
                #print((im_msgtype, im_mbz, socket.inet_ntoa(im_src), socket.inet_ntoa(im_dst)))

                ip_src = socket.inet_ntoa(im_src)
                ip_dst = socket.inet_ntoa(im_dst)

                if im_msgtype == Kernel.IGMPMSG_NOCACHE:
                    print("IGMP NO CACHE")
                    self.igmpmsg_nocache_handler(ip_src, ip_dst, im_vif)
                elif im_msgtype == Kernel.IGMPMSG_WRONGVIF:
                    print("WRONG VIF HANDLER")
                    self.igmpmsg_wrongvif_handler(ip_src, ip_dst, im_vif)
                #elif im_msgtype == Kernel.IGMPMSG_WHOLEPKT:
                #    print("IGMP_WHOLEPKT")
                #    self.igmpmsg_wholepacket_handler(ip_src, ip_dst)
                else:
                    raise Exception
            except Exception:
                traceback.print_exc()
                continue

    # receive multicast (S,G) packet and multicast routing table has no (S,G) entry
    def igmpmsg_nocache_handler(self, ip_src, ip_dst, iif):
        unicast_route = UnicastRouting.get_route(ip_src)
        next_hop = unicast_route["gateway"]
        is_directly_connected = next_hop is None
        if not is_directly_connected:
            return

        source_group_pair = (ip_src, ip_dst)
        with self.rwlock.genWlock():
            if ip_src in self.routing and ip_dst in self.routing[ip_src]:
                self.routing[ip_src][ip_dst].recv_data_msg(iif)
            else:
                kernel_entry = KernelEntry(ip_src, ip_dst)
                if ip_src not in self.routing:
                    self.routing[ip_src] = {}

                self.routing[ip_src][ip_dst] = kernel_entry
                kernel_entry.recv_data_msg(iif)

    # receive multicast (S,G) packet in a outbound_interface
    def igmpmsg_wrongvif_handler(self, ip_src, ip_dst, iif):
        #source_group_pair = (ip_src, ip_dst)
        #self.get_routing_entry(source_group_pair, create_if_not_existent=True).recv_data_msg(iif)
        return


    ''' useless in PIM-DM... useful in PIM-SM
    def igmpmsg_wholepacket_handler(self, ip_src, ip_dst):
        #kernel_entry = self.routing[(ip_src, ip_dst)]
        source_group_pair = (ip_src, ip_dst)
        self.get_routing_entry(source_group_pair, create_if_not_existent=True).recv_data_msg()
        #kernel_entry.recv_data_msg(iif)
    '''



    def get_routing_entry(self, source_group: tuple, create_if_not_existent=True):
        ip_src = source_group[0]
        ip_dst = source_group[1]
        with self.rwlock.genRlock():
            if ip_src in self.routing and ip_dst in self.routing[ip_src]:
                return self.routing[ip_src][ip_dst]

        with self.rwlock.genWlock():
            if ip_src in self.routing and ip_dst in self.routing[ip_src]:
                return self.routing[ip_src][ip_dst]
            elif create_if_not_existent:
                kernel_entry = KernelEntry(ip_src, ip_dst)
                if ip_src not in self.routing:
                    self.routing[ip_src] = {}

                self.routing[ip_src][ip_dst] = kernel_entry
                return kernel_entry
            else:
                return None

    # notify KernelEntries about changes at the unicast routing table
    def notify_unicast_changes(self, subnet):
        with self.rwlock.genWlock():
            for source_ip in list(self.routing.keys()):
                source_ip_obj = ipaddress.ip_address(source_ip)
                if source_ip_obj not in subnet:
                    continue
                for group_ip in list(self.routing[source_ip].keys()):
                    self.routing[source_ip][group_ip].network_update()





    def recv_install_or_uninstall_msg(self, source_group, interface: "InterfaceProtocol"):
        ip_src = source_group[0]
        ip_dst = source_group[1]

        interest_state = False
        upstream_state = None
        with self.rwlock.genWlock():
            for n in interface.neighbors.values():
                (neighbor_interest_state, neighbor_upstream_state) = n.get_tree_state(tree=source_group)
                if not interest_state and neighbor_interest_state:
                    interest_state = neighbor_interest_state

                if neighbor_upstream_state is not None:
                    if upstream_state is None:
                        upstream_state = neighbor_upstream_state
                    elif neighbor_upstream_state.is_better_than(upstream_state):
                        upstream_state = neighbor_upstream_state


            tree_is_active = upstream_state is not None
            print("RCV INSTALL/UNINSTALL")
            print("INTERESSE: ", interest_state)
            if tree_is_active:
                if ip_src not in self.routing:
                    self.routing[ip_src] = {}
                    self.routing[ip_src][ip_dst] = KernelEntry(ip_src, ip_dst)
                    # todo send install and interest state
                    self.routing[ip_src][ip_dst].check_interface_state(interface.vif_index, upstream_state, interest_state)
                elif ip_dst not in self.routing[ip_src]:
                    self.routing[ip_src][ip_dst] = KernelEntry(ip_src, ip_dst)
                    # todo send install and interest state
                    self.routing[ip_src][ip_dst].check_interface_state(interface.vif_index, upstream_state, interest_state)

                else:
                    # todo notify possible change of install
                    self.routing[ip_src][ip_dst].check_interface_state(interface.vif_index, upstream_state, interest_state)
            else:
                if ip_src in self.routing and ip_dst in self.routing[ip_src]:
                    # todo notify kernel entry about tree to be removed
                    self.routing[ip_src][ip_dst].check_interface_state(interface.vif_index, upstream_state, interest_state)

    def recv_interest_msg(self, source_group, interface: "InterfaceProtocol"):
        ip_src = source_group[0]
        ip_dst = source_group[1]

        interest_state = False
        #upstream_state = None
        with self.rwlock.genRlock():
            if ip_src not in self.routing or ip_dst not in self.routing[ip_src]:
                return

            for n in interface.neighbors.values():
                (neighbor_interest_state, _) = n.get_tree_state(tree=source_group)
                if not interest_state and neighbor_interest_state:
                    interest_state = neighbor_interest_state
                    break

            self.routing[ip_src][ip_dst].check_interest_state(interface.vif_index, interest_state)

    def recv_ack_msg(self, source_group, interface, packet):
        (ip_src, ip_dst) = source_group
        with self.rwlock.genRlock():
            if ip_src in self.routing and ip_dst in self.routing[ip_src]:
                self.routing[ip_src][ip_dst].recv_ack_msg(interface.vif_index, packet)

    def recheck_all_trees(self, interface: "InterfaceProtocol"):
        with self.rwlock.genWlock():
            for (source, src_dict) in self.routing.items():
                for (group, entry) in src_dict.values():
                    interest_state = False
                    upstream_state = None
                    for n in interface.neighbors.values():
                        (neighbor_interest_state, neighbor_upstream_state) = n.get_tree_state(tree=(source, group))

                        if not interest_state and neighbor_interest_state:
                            interest_state = neighbor_interest_state

                        if neighbor_upstream_state is not None:
                            if upstream_state is None:
                                upstream_state = neighbor_upstream_state
                            elif neighbor_upstream_state.is_better_than(upstream_state):
                                upstream_state = neighbor_upstream_state

                    entry.check_interface_state(interface.vif_index, upstream_state, interest_state)


    # notify about changes at the interface (IP)
    '''
    def notify_interface_change(self, interface_name):
        with self.interface_lock:
            # check if interface was already added
            if interface_name not in self.vif_name_to_index_dic:
                return

            print("trying to change ip")
            pim_interface = self.pim_interface.get(interface_name)
            if pim_interface:
                old_ip = pim_interface.get_ip()
                pim_interface.change_interface()
                new_ip = pim_interface.get_ip()
                if old_ip != new_ip:
                    self.vif_dic[new_ip] = self.vif_dic.pop(old_ip)

            igmp_interface = self.igmp_interface.get(interface_name)
            if igmp_interface:
                igmp_interface.change_interface()
    '''

    # Neighbor removal at interface vif_index
    def remove_tree(self, source, group):
        with self.rwlock.genWlock():
            if source in self.routing and group in self.routing[source]:
                #self.routing[source][group].delete()
                self.routing[source][group].remove_entry()

    # Neighbor removal at interface vif_index
    def interface_neighbor_removal(self, vif_index, other_neighbors_remain):
        with self.rwlock.genRlock():
            for groups_dict in self.routing.values():
                for entry in groups_dict.values():
                    entry.neighbor_removal(vif_index, other_neighbors_remain)


    def new_neighbor(self, interface):
        trees_to_sync = {}
        vif_index = interface.vif_index
        with self.rwlock.genWlock():
            for (ip_src, src_dict) in self.routing.items():
                for (ip_dst, kernel_entry) in self.routing[ip_src].items():
                    tree = kernel_entry.get_interface_sync_state(vif_index)
                    if tree is not None:
                        trees_to_sync[(ip_src, ip_dst)] = tree
            return trees_to_sync



    '''
        list_of_trees = []
        pat = PacketProtocolActiveTrees()
        with self.rwlock.genRlock():
            for source_ip in self.routing.keys():
                for group_ip in list(self.routing[source_ip].keys()):
                    list_of_trees.append({"SOURCE": source_ip, "GROUP": group_ip})


            if len(list_of_trees) == 0:
                return

            # TODO MELHORAR A ADICAO DE ARVORES
            pat.trees = list_of_trees
            pckt = Packet(payload=PacketProtocolHeader(payload=pat))
            interface.send_reliably(data=pckt, group_ip=neighbor_ip)
        return
    '''

    '''
    def receive_active_trees(self, trees):
        trees_to_confirm = set()
        for tree in trees:
            # first check if tree directly connected
            (source, _) = tree
            root_interface = self.protocol_interface[self.vif_index_to_name_dic[self.vif_dic[UnicastRouting.check_rpf(source)]]]  # type: InterfaceProtocol
            netifaces_interface = netifaces.ifaddresses(root_interface.interface_name)[netifaces.AF_INET][0]
            if ipaddress.ip_address(source) in ipaddress.ip_interface(netifaces_interface['addr'] + '/' + netifaces_interface['netmask']).network:
                self.get_routing_entry(tree, create_if_not_existent=True)
                continue

            trees_to_confirm.add(tree)
        self.flood_confirm_tree(trees_to_confirm)
    '''
    '''
    def flood_confirm_tree(self, trees):
        with self.rwlock.genRlock():
            for tree in trees:
                (source, group) = tree
                print("tree:", source, group)
                if source in self.routing and group in self.routing[source]:
                    # check if I already know tree
                    continue
                pkt_confirm = PacketProtocolConfirm(source, group)
                pkt = PacketProtocolHeader(payload=pkt_confirm)
                for interface in self.protocol_interface.values():
                    interface.send(pkt)

    def receive_confirm(self, packet):
        recv_interface = packet.interface
        pkt_confirm = packet.payload.payload
        source = pkt_confirm.source
        group = pkt_confirm.group

        root_interface = self.protocol_interface[self.vif_index_to_name_dic[self.vif_dic[UnicastRouting.check_rpf(source)]]] # type: InterfaceProtocol

        netifaces_interface = netifaces.ifaddresses(root_interface.interface_name)[netifaces.AF_INET][0]
        if ipaddress.ip_address(source) in ipaddress.ip_interface(netifaces_interface['addr'] + '/' + netifaces_interface['netmask']).network:
            if source in self.routing and group in self.routing[source]:
                pkt_set_tree = PacketProtocolSetTree(source, group)
                pkt = PacketProtocolHeader(payload=pkt_set_tree)
            else:
                pkt_remove_tree = PacketProtocolRemoveTree(source, group)
                pkt = PacketProtocolHeader(payload=pkt_remove_tree)
            recv_interface.send_reliably(Packet(payload=pkt))
        else:
            # TODO SEND CONFIRM RELIABLY
            #root_interface.send(packet.payload)
            #root_interface.send(Packet(payload=packet.payload))
            pkt = PacketProtocolHeader(payload=pkt_confirm)
            root_interface.send_reliably(Packet(payload=pkt))


    def receive_remove_tree(self, packet):
        recv_interface = packet.interface
        pkt_remove = packet.payload.payload
        source = pkt_remove.source
        group = pkt_remove.group

        # todo melhoria: comparar pelo ip do rpf
        root_interface = self.protocol_interface[self.vif_index_to_name_dic[self.vif_dic[UnicastRouting.check_rpf(source)]]] # type: InterfaceProtocol
        if recv_interface != root_interface:
            return


        self.remove_tree(source, group)
        # todo lock de interfaces
        for interface in self.protocol_interface.values():
            if interface == recv_interface:
                continue

            pkt = PacketProtocolHeader(payload=pkt_remove)
            interface.send_reliably(Packet(payload=pkt))

    def receive_set_tree(self, packet):
        recv_interface = packet.interface
        pkt_set_tree = packet.payload.payload
        source = pkt_set_tree.source
        group = pkt_set_tree.group

        # todo melhoria: comparar pelo ip do rpf
        root_interface = self.protocol_interface[self.vif_index_to_name_dic[self.vif_dic[UnicastRouting.check_rpf(source)]]] # type: InterfaceProtocol
        if recv_interface != root_interface:
            return

        tree = self.get_routing_entry((source, group), create_if_not_existent=True)
        # todo lock de interfaces
        for interface in self.protocol_interface.values():
            if interface == recv_interface:
                continue

            pkt = PacketProtocolHeader(payload=pkt_set_tree)
            interface.send_reliably(Packet(payload=pkt))

    '''
    '''
    # When new neighbor connects try to resend last state refresh msg (if AssertWinner)
    def new_or_reset_neighbor(self, vif_index, neighbor_ip):
        with self.rwlock.genRlock():
            for groups_dict in self.routing.values():
                for entry in groups_dict.values():
                    entry.new_or_reset_neighbor(vif_index, neighbor_ip)
    '''
