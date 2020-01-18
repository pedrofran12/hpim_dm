import socket
import struct
from threading import Thread
import traceback
import ipaddress
from hpimdm import UnicastRouting

from hpimdm.RWLock.RWLock import RWLockWrite
from hpimdm import Main

from hpimdm.InterfaceProtocol import InterfaceProtocol
from hpimdm.InterfaceIGMP import InterfaceIGMP
from hpimdm.tree.KernelEntry import KernelEntry, KernelEntryOriginator, KernelEntryNonOriginator
from hpimdm.tree import protocol_globals

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

        for source_dict in list(self.routing.values()):
            for kernel_entry in list(source_dict.values()):
                kernel_entry.new_interface(index)

        self.interface_logger.debug('Create virtual interface: %s -> %d', interface_name, index)
        return index

    def create_protocol_interface(self, interface_name: str):
        thread = None
        with self.rwlock.genWlock():
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

            if interface_name not in self.protocol_interface:
                pim_interface = InterfaceProtocol(interface_name, index)
                self.protocol_interface[interface_name] = pim_interface
                ip_interface = pim_interface.ip_interface
                if not vif_already_exists:
                    self.create_virtual_interface(ip_interface=ip_interface, interface_name=interface_name, index=index)
                pim_interface.enable()
                thread = Thread(target=self.recheck_all_trees, args=(index,))
                thread.start()

        if thread is not None:
            thread.join()

    def create_igmp_interface(self, interface_name: str):
        thread = None
        with self.rwlock.genWlock():
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

            if interface_name not in self.igmp_interface:
                igmp_interface = InterfaceIGMP(interface_name, index)
                self.igmp_interface[interface_name] = igmp_interface
                ip_interface = igmp_interface.ip_interface
                if not vif_already_exists:
                    self.create_virtual_interface(ip_interface=ip_interface, interface_name=interface_name, index=index)
                igmp_interface.enable()
                thread = Thread(target=self.recheck_igmp_all_trees, args=(index,))
                thread.start()

        if thread is not None:
            thread.join()

    def remove_interface(self, interface_name, igmp: bool = False, pim: bool = False):
        thread = None
        with self.rwlock.genWlock():
            ip_interface = None
            pim_interface = self.protocol_interface.get(interface_name)
            igmp_interface = self.igmp_interface.get(interface_name)
            if (not igmp and not pim) or (interface_name not in self.vif_name_to_index_dic):
                return
            if pim and pim_interface is not None:
                pim_interface = self.protocol_interface.pop(interface_name)
                ip_interface = pim_interface.ip_interface
                pim_interface.remove()
            if igmp and igmp_interface is not None:
                igmp_interface = self.igmp_interface.pop(interface_name)
                ip_interface = igmp_interface.ip_interface
                igmp_interface.remove()

            if interface_name not in self.igmp_interface and interface_name not in self.protocol_interface:
                self.remove_virtual_interface(ip_interface)
            else:
                vif_index = self.vif_name_to_index_dic.get(interface_name)
                thread = Thread(target=self.recheck_all_trees, args=(vif_index,))
                thread.start()

        if thread is not None:
            thread.join()

    def remove_virtual_interface(self, ip_interface):
        index = self.vif_dic.pop(ip_interface, None)
        struct_vifctl = struct.pack("HBBI 4s 4s", index, 0, 0, 0, socket.inet_aton("0.0.0.0"), socket.inet_aton("0.0.0.0"))

        try:
            self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_DEL_VIF, struct_vifctl)
        except socket.error:
            pass

        interface_name = self.vif_index_to_name_dic.pop(index, None)
        self.vif_name_to_index_dic.pop(interface_name, None)

        # remove this interface from KernelEntries
        for source_dict in list(self.routing.values()):
            for kernel_entry in list(source_dict.values()):
                kernel_entry.remove_interface(index)

        self.interface_logger.debug('Remove virtual interface: %s -> %d', interface_name, index)

    def notify_interface_changes(self, interface_name):
        with self.rwlock.genWlock():
            if interface_name is None or interface_name not in self.vif_name_to_index_dic:
                return
            igmp_was_enabled = interface_name in self.igmp_interface
            protocol_was_enabled = interface_name in self.protocol_interface

        self.remove_interface(interface_name, igmp=True, pim=True)
        if igmp_was_enabled:
            self.create_igmp_interface(interface_name)
        if protocol_was_enabled:
            self.create_protocol_interface(interface_name)

    def add_interface_security(self, interface_name, security_id, security_algorithm, security_key):
        with self.rwlock.genRlock():
            if interface_name not in self.protocol_interface:
                return

            interface = self.protocol_interface.get(interface_name) #type: InterfaceProtocol
            interface.add_security_key(security_id, security_algorithm, security_key)

    def remove_interface_security(self, interface_name, security_id):
        with self.rwlock.genRlock():
            if interface_name not in self.protocol_interface:
                return

            interface = self.protocol_interface.get(interface_name) #type: InterfaceProtocol
            interface.remove_security_key(security_id)

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

    def set_flood_multicast_route(self, source_ip, group_ip, inbound_interface_index):
        if inbound_interface_index is None:
            return
        source_ip = socket.inet_aton(source_ip)
        group_ip = socket.inet_aton(group_ip)

        outbound_interfaces = [1]*self.MAXVIFS
        outbound_interfaces[inbound_interface_index] = 0

        #outbound_interfaces_and_other_parameters = list(kernel_entry.outbound_interfaces) + [0]*4
        outbound_interfaces_and_other_parameters = outbound_interfaces + [0]*3 + [protocol_globals.INITIAL_FLOOD_TIME]

        #outbound_interfaces, 0, 0, 0, 0 <- only works with python>=3.5
        #struct_mfcctl = struct.pack("4s 4s H " + "B"*Kernel.MAXVIFS + " IIIi", source_ip, group_ip, inbound_interface_index, *outbound_interfaces, 0, 0, 0, 0)
        struct_mfcctl = struct.pack("4s 4s H " + "B"*Kernel.MAXVIFS + " IIIi", source_ip, group_ip, inbound_interface_index, *outbound_interfaces_and_other_parameters)
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
            try:
                self.socket.setsockopt(socket.IPPROTO_IP, Kernel.MRT_DEL_MFC, struct_mfcctl)
            except socket.error:
                pass
            self.routing[kernel_entry.source_ip].pop(kernel_entry.group_ip)
            kernel_entry.delete_state()
            if len(self.routing[source_ip]) == 0:
                self.routing.pop(source_ip)

            info_about_tree_can_be_removed = True
            for interface in self.protocol_interface.values():
                if not info_about_tree_can_be_removed:
                    break
                for n in list(interface.neighbors.values()):
                    (_, neighbor_upstream_state) = n.get_tree_state(tree=(source_ip, group_ip))
                    if neighbor_upstream_state is not None:
                        self.create_entry(kernel_entry.source_ip, kernel_entry.group_ip)
                        info_about_tree_can_be_removed = False
                        break

            if info_about_tree_can_be_removed:
                for interface in self.protocol_interface.values():
                    interface.remove_tree_state(kernel_entry.source_ip, kernel_entry.group_ip)

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
        (_, _, is_directly_connected, rpf_if) = UnicastRouting.get_unicast_info(ip_src)

        with self.rwlock.genWlock():
            if ip_src in self.routing and ip_dst in self.routing[ip_src]:
                self.routing[ip_src][ip_dst].recv_data_msg(iif)
            elif is_directly_connected:
                if protocol_globals.INITIAL_FLOOD_ENABLED:
                    # flood
                    self.set_flood_multicast_route(ip_src, ip_dst, rpf_if)
                if rpf_if is not None:
                    self.create_entry(ip_src, ip_dst)
                    self.routing[ip_src][ip_dst].recv_data_msg(iif)
            elif not is_directly_connected and protocol_globals.INITIAL_FLOOD_ENABLED:
                # flood
                self.set_flood_multicast_route(ip_src, ip_dst, rpf_if)



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

    # notify KernelEntries about changes at the unicast routing table
    def notify_unicast_changes(self, subnet):
        with self.rwlock.genWlock():
            for source_ip in list(self.routing.keys()):
                source_ip_obj = ipaddress.ip_address(source_ip)
                if source_ip_obj not in subnet:
                    continue
                for group_ip in list(self.routing[source_ip].keys()):
                    self.routing[source_ip][group_ip].network_update()

    def recv_upstream_msg(self, source_group, interface: "InterfaceProtocol"):
        ip_src = source_group[0]
        ip_dst = source_group[1]

        print("ENTROU RCV_UPSTREAM")
        with self.rwlock.genWlock():
            if interface not in self.protocol_interface.values():
                return

            (interest_state, upstream_state) = interface.get_tree_state(source_group)
            tree_is_not_inactive = upstream_state is not None
            print("RCV INSTALL/UNINSTALL")
            print("INTERESSE: ", interest_state)

            if tree_is_not_inactive and (ip_src not in self.routing or ip_dst not in self.routing.get(ip_src, {})):
                self.create_entry(ip_src, ip_dst)
            elif ip_src in self.routing and ip_dst in self.routing[ip_src]:
                self.routing[ip_src][ip_dst].check_interface_state(interface.vif_index, upstream_state, interest_state)
            else:
                interface.remove_tree_state(ip_src, ip_dst)
        print("SAIU RCV_UPSTREAM")

    def recv_interest_msg(self, source_group, interface: "InterfaceProtocol"):
        ip_src = source_group[0]
        ip_dst = source_group[1]

        print("ENTROU RECV_INTEREST")
        with self.rwlock.genRlock():
            if interface not in self.protocol_interface.values():
                return

            if ip_src not in self.routing or ip_dst not in self.routing[ip_src]:
                interface.remove_tree_state(ip_src, ip_dst)
                return

            (interest_state, upstream_state) = interface.get_tree_state(source_group)
            self.routing[ip_src][ip_dst].check_interest_state(interface.vif_index, interest_state)
        print("SAIU RECV_INTEREST")

    def create_entry(self, ip_src, ip_dst):
        (_, _, is_directly_connected, _) = UnicastRouting.get_unicast_info(ip_src)

        upstream_state_dict = {}
        interest_state_dict = {}
        for interface in self.protocol_interface.values():
            (interest_state, upstream_state) = interface.get_tree_state((ip_src, ip_dst))
            upstream_state_dict[interface.vif_index] = upstream_state
            interest_state_dict[interface.vif_index] = interest_state

        other_interfaces = self.protocol_interface.keys() - self.vif_name_to_index_dic.keys()
        for interface_name in other_interfaces:
            vif_index = self.vif_name_to_index_dic.get(interface_name)
            upstream_state_dict[vif_index] = None
            interest_state_dict[vif_index] = False

        if ip_src not in self.routing:
            self.routing[ip_src] = {}

        if ip_dst not in self.routing[ip_src] and is_directly_connected:
            self.routing[ip_src][ip_dst] = KernelEntryOriginator(ip_src, ip_dst, upstream_state_dict, interest_state_dict)
        elif ip_dst not in self.routing[ip_src]:
            self.routing[ip_src][ip_dst] = KernelEntryNonOriginator(ip_src, ip_dst, upstream_state_dict, interest_state_dict)

    def snapshot_multicast_routing_table(self, vif_index):
        trees_to_sync = {}
        print("ENTROU SNAPSHOT")
        #with self.rwlock.genWlock():
        for (ip_src, src_dict) in self.routing.items():
            for (ip_dst, kernel_entry) in self.routing[ip_src].items():
                tree = kernel_entry.get_interface_sync_state(vif_index)
                if tree is not None:
                    trees_to_sync[(ip_src, ip_dst)] = tree
        print("SAIU SNAPSHOT")
        return trees_to_sync

    def recheck_all_trees(self, vif_index: int):
        print("ENTROU RECHECK")
        with self.rwlock.genWlock():
            interface_name = self.vif_index_to_name_dic.get(vif_index, None)
            interface = self.protocol_interface.get(interface_name, None)

            known_trees = set()
            if interface is not None:
                for n in list(interface.neighbors.values()):
                    known_trees = known_trees.union(n.get_known_trees())

            for (source, src_dict) in self.routing.items():
                for group in src_dict.keys():
                    known_trees.add((source, group))

            print("KNOWN TREES: ", known_trees)
            #print("INDEX:", interface.vif_index)

            for tree in known_trees:
                if interface is not None:
                    (interest_state, upstream_state) = interface.get_tree_state(tree)
                else:
                    (interest_state, upstream_state) = (False, None)

                print("UPSTREAM_STATE:", upstream_state)
                print("INTEREST_STATE:", interest_state)
                if upstream_state is not None and (tree[0] not in self.routing or tree[1] not in self.routing.get(tree[0], {})):
                    self.create_entry(tree[0], tree[1])
                elif tree[0] in self.routing and tree[1] in self.routing[tree[0]]:
                        self.routing[tree[0]][tree[1]].check_interface_state(vif_index, upstream_state, interest_state)
        print("SAIU RECHECK")

    def recheck_igmp_all_trees(self, vif_index: int):
        print("ENTROU RECHECK IGMP")
        with self.rwlock.genWlock():
            for src_dict in self.routing.values():
                for entry in src_dict.values():
                    entry.check_igmp_state(vif_index)
            print("SAIU RECHECK IGMP")

    def recheck_all_trees_in_all_interfaces(self):
        for i in list(self.vif_dic.values()):
            self.recheck_all_trees(i)
