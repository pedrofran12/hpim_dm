import time
import socket
import struct
import logging
import ipaddress
import netifaces
from threading import RLock
from socket import if_nametoindex

from hpimdm import Main
from .packet.Packet import Packet
from .Interface import Interface
from .InterfaceHPIM import InterfaceHPIM
from .packet.ReceivedPacket import ReceivedPacket_v6
from hpimdm.tree.hpim_globals import MSG_FORMAT
if MSG_FORMAT == "BINARY":
    from hpimdm.packet.PacketHPIMHeader import PacketHPIMHeader_v6
    from hpimdm.packet.PacketHPIMIamUpstream import PacketHPIMUpstream_v6
    from hpimdm.packet.PacketHPIMNotUpstream import PacketHPIMNoLongerUpstream_v6
    from hpimdm.packet.PacketHPIMInterest import PacketHPIMInterest_v6
    from hpimdm.packet.PacketHPIMInterest import PacketHPIMNoInterest_v6
    from hpimdm.packet.PacketHPIMSync import PacketHPIMSyncEntry_v6, PacketHPIMSync_v6
    from hpimdm.packet.PacketHPIMAck import PacketHPIMAck_v6
else:
    from hpimdm.packet.PacketHPIMHeader import PacketHPIMHeaderJson as PacketHPIMHeader_v6
    from hpimdm.packet.PacketHPIMIamUpstream import PacketHPIMUpstreamJson as PacketHPIMUpstream_v6
    from hpimdm.packet.PacketHPIMNotUpstream import PacketHPIMNoLongerUpstreamJson as PacketHPIMNoLongerUpstream_v6
    from hpimdm.packet.PacketHPIMInterest import PacketHPIMInterestJson as PacketHPIMInterest_v6
    from hpimdm.packet.PacketHPIMInterest import PacketHPIMNoInterestJson as PacketHPIMNoInterest_v6
    from hpimdm.packet.PacketHPIMSync import PacketHPIMSyncEntryJson as PacketHPIMSyncEntry_v6,\
        PacketHPIMSyncJson as PacketHPIMSync_v6
    from hpimdm.packet.PacketHPIMAck import PacketHPIMAckJson as PacketHPIMAck_v6


class InterfaceHPIM6(InterfaceHPIM):
    MCAST_GRP = "ff02::d"

    def __init__(self, interface_name: str, vif_index: int):
        self.interface_logger = logging.LoggerAdapter(InterfaceHPIM.LOGGER, {'vif': vif_index,
                                                                             'interfacename': interface_name})

        # Generate BootTime
        self.time_of_boot = int(time.time())

        # Regulate transmission of Hello messages
        self.hello_timer = None

        # protocol neighbors
        self._had_neighbors = False
        self.neighbors = {}
        self.neighbors_lock = RLock()

        # reliable transmission buffer
        self.reliable_transmission_buffer = {} # Key: ID da msg ; value: ReliableMsgTransmission
        self.reliable_transmission_lock = RLock()

        # sequencer for msg reliability
        self.sequencer = 0
        self.sequencer_lock = RLock()

        # security
        self.security_id = 0
        self.security_len = 0
        self.hash_function = None
        self.security_key = b''

        # SOCKET
        s = socket.socket(socket.AF_INET6, socket.SOCK_RAW, socket.IPPROTO_PIM)

        ip_interface = "::"
        for if_addr in netifaces.ifaddresses(interface_name)[netifaces.AF_INET6]:
            ip_interface = if_addr["addr"]
            if ipaddress.IPv6Address(ip_interface.split("%")[0]).is_link_local:
                # bind to interface
                s.bind(socket.getaddrinfo(ip_interface, None, 0, socket.SOCK_RAW, 0, socket.AI_PASSIVE)[0][4])
                ip_interface = ip_interface.split("%")[0]
                break

        self.ip_interface = ip_interface

        # allow other sockets to bind this port too
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

        # explicitly join the multicast group on the interface specified
        if_index = if_nametoindex(interface_name)
        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_JOIN_GROUP,
                     socket.inet_pton(socket.AF_INET6, InterfaceHPIM6.MCAST_GRP) + struct.pack('@I', if_index))
        s.setsockopt(socket.SOL_SOCKET, 25, str(interface_name + '\0').encode('utf-8'))

        # set socket output interface
        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_MULTICAST_IF, struct.pack('@I', if_index))

        # set socket TTL to 1
        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_MULTICAST_HOPS, 1)
        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_UNICAST_HOPS, 1)

        # don't receive outgoing packets
        s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_MULTICAST_LOOP, 0)
        Interface.__init__(self, interface_name, s, s, vif_index)
        self.force_send_hello()

    @staticmethod
    def get_kernel():
        """
        Get Kernel object
        """
        return Main.kernel_v6

    @staticmethod
    def _get_address_family():
        """
        Get address family for this interface
        """
        return socket.AF_INET6

    @staticmethod
    def get_ip_header_length():
        """"
        Method for getting fixed IPv6 header length. Useful for doing calculations with MTU
        """
        return 40

    def send(self, data: bytes, group_ip: str=MCAST_GRP):
        """
        Send a new packet destined to group_ip IP
        """
        super().send(data=data, group_ip=group_ip)

    def _receive(self, raw_bytes, ancdata, src_addr):
        """
        Interface received a new control packet
        """
        if raw_bytes:
            packet = ReceivedPacket_v6(raw_bytes, ancdata, src_addr, 103, self)
            self.PKT_FUNCTIONS[packet.payload.get_pim_type()](self, packet)

    ###########################################
    # Create packets
    ###########################################
    def create_i_am_upstream_msg(self, my_boot_time, sn, source, group, metric_preference, metric):
        ph = PacketHPIMUpstream_v6(source, group, metric_preference, metric, sn)
        return Packet(payload=PacketHPIMHeader_v6(payload=ph, boot_time=my_boot_time))

    def create_i_am_no_longer_upstream_msg(self, my_boot_time, sn, source, group):
        ph = PacketHPIMNoLongerUpstream_v6(source, group, sn)
        return Packet(payload=PacketHPIMHeader_v6(payload=ph, boot_time=my_boot_time))

    def create_interest_msg(self, my_boot_time, sn, source, group):
        ph = PacketHPIMInterest_v6(source, group, sn)
        return Packet(payload=PacketHPIMHeader_v6(payload=ph, boot_time=my_boot_time))

    def create_no_interest_msg(self, my_boot_time, sn, source, group):
        ph = PacketHPIMNoInterest_v6(source, group, sn)
        return Packet(payload=PacketHPIMHeader_v6(payload=ph, boot_time=my_boot_time))

    def create_ack_msg(self, my_boot_time, sn, source, group, neighbor_boot_time,
                       neighbor_snapshot_sn, my_snapshot_sn):
        ack = PacketHPIMAck_v6(source_ip=source, group_ip=group, sequence_number=sn,
                               neighbor_boot_time=neighbor_boot_time, neighbor_snapshot_sn=neighbor_snapshot_sn,
                               my_snapshot_sn=my_snapshot_sn)
        return Packet(payload=PacketHPIMHeader_v6(payload=ack, boot_time=my_boot_time))

    def create_sync_entry_hdr(self, source, group, metric_preference, metric):
        return PacketHPIMSyncEntry_v6(source, group, metric_preference, metric)

    def create_sync_msg(self, my_boot_time, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, upstream_trees,
                        master_flag, more_flag, neighbor_boot_time):
        pkt_sync = PacketHPIMSync_v6(my_snapshot_sn, neighbor_snapshot_sn, sync_sn, upstream_trees,
                                     master_flag, more_flag, neighbor_boot_time)
        return Packet(payload=PacketHPIMHeader_v6(pkt_sync, my_boot_time))
