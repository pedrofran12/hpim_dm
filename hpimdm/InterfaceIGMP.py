import socket
import struct
import netifaces
from ipaddress import IPv4Address
from ctypes import create_string_buffer, addressof

from hpimdm.packet.ReceivedPacket import ReceivedPacket
from hpimdm.Interface import Interface
from hpimdm.igmp.igmp_globals import VERSION_1_MEMBERSHIP_REPORT, VERSION_2_MEMBERSHIP_REPORT, LEAVE_GROUP,\
    MEMBERSHIP_QUERY
if not hasattr(socket, 'SO_BINDTODEVICE'):
    socket.SO_BINDTODEVICE = 25

ETH_P_IP = 0x0800		# Internet Protocol packet
SO_ATTACH_FILTER = 26


class InterfaceIGMP(Interface):
    FILTER_IGMP = [
        struct.pack('HBBI', 0x28, 0, 0, 0x0000000c),
        struct.pack('HBBI', 0x15, 0, 3, 0x00000800),
        struct.pack('HBBI', 0x30, 0, 0, 0x00000017),
        struct.pack('HBBI', 0x15, 0, 1, 0x00000002),
        struct.pack('HBBI', 0x6, 0, 0, 0x00040000),
        struct.pack('HBBI', 0x6, 0, 0, 0x00000000),
    ]

    def __init__(self, interface_name: str, vif_index: int):
        self.ip_interface = netifaces.ifaddresses(interface_name)[netifaces.AF_INET][0]['addr']

        # SEND SOCKET
        snd_s = socket.socket(socket.AF_INET, socket.SOCK_RAW, socket.IPPROTO_IGMP)

        # bind to interface
        snd_s.setsockopt(socket.SOL_SOCKET, socket.SO_BINDTODEVICE, str(interface_name + "\0").encode('utf-8'))

        # RECEIVE SOCKET
        rcv_s = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(ETH_P_IP))

        # receive only IGMP packets by setting a BPF filter
        bpf_filter = b''.join(InterfaceIGMP.FILTER_IGMP)
        b = create_string_buffer(bpf_filter)
        mem_addr_of_filters = addressof(b)
        fprog = struct.pack('HL', len(InterfaceIGMP.FILTER_IGMP), mem_addr_of_filters)
        rcv_s.setsockopt(socket.SOL_SOCKET, SO_ATTACH_FILTER, fprog)

        # bind to interface
        rcv_s.bind((interface_name, ETH_P_IP))
        super().__init__(interface_name=interface_name, recv_socket=rcv_s, send_socket=snd_s, vif_index=vif_index)
        self.interface_enabled = True
        from hpimdm.igmp.RouterState import RouterState
        self.interface_state = RouterState(self)

    @staticmethod
    def _get_address_family():
        return socket.AF_INET

    def get_ip(self):
        """
        Get IP of this interface
        :return:
        """
        return self.ip_interface

    def send(self, data: bytes, address: str="224.0.0.1"):
        """
        Send a new control packet destined to address
        """
        super().send(data, address)

    def _receive(self, raw_bytes, ancdata, src_addr):
        """
        Interface received a new control packet
        """
        if raw_bytes:
            raw_bytes = raw_bytes[14:]
            packet = ReceivedPacket(raw_bytes, self)
            ip_src = packet.ip_header.ip_src
            if not (ip_src == "0.0.0.0" or IPv4Address(ip_src).is_multicast):
                self.PKT_FUNCTIONS.get(packet.payload.get_igmp_type(), InterfaceIGMP.receive_unknown_type)(self, packet)

    ###########################################
    # Recv packets
    ###########################################
    def receive_version_1_membership_report(self, packet):
        """
        Interface received an IGMP Version 1 Membership Report packet
        """
        ip_dst = packet.ip_header.ip_dst
        igmp_group = packet.payload.group_address
        if ip_dst == igmp_group and IPv4Address(igmp_group).is_multicast:
            self.interface_state.receive_v1_membership_report(packet)

    def receive_version_2_membership_report(self, packet):
        """
        Interface received an IGMP Membership Report packet
        """
        ip_dst = packet.ip_header.ip_dst
        igmp_group = packet.payload.group_address
        if ip_dst == igmp_group and IPv4Address(igmp_group).is_multicast:
            self.interface_state.receive_v2_membership_report(packet)

    def receive_leave_group(self, packet):
        """
        Interface received an IGMP Leave packet
        """
        ip_dst = packet.ip_header.ip_dst
        igmp_group = packet.payload.group_address
        if ip_dst == "224.0.0.2" and IPv4Address(igmp_group).is_multicast:
            self.interface_state.receive_leave_group(packet)

    def receive_membership_query(self, packet):
        """
        Interface received an IGMP Query packet
        """
        ip_dst = packet.ip_header.ip_dst
        igmp_group = packet.payload.group_address
        if (IPv4Address(igmp_group).is_multicast and ip_dst == igmp_group) or \
                (ip_dst == "224.0.0.1" and igmp_group == "0.0.0.0"):
            self.interface_state.receive_query(packet)

    def receive_unknown_type(self, packet):
        """
        Interface received an IGMP Unknown packet
        """
        return

    PKT_FUNCTIONS = {
        VERSION_1_MEMBERSHIP_REPORT: receive_version_1_membership_report,
        VERSION_2_MEMBERSHIP_REPORT: receive_version_2_membership_report,
        LEAVE_GROUP: receive_leave_group,
        MEMBERSHIP_QUERY: receive_membership_query,
    }

    ##################
    def remove(self):
        """
        Remove this interface
        Clear all state
        """
        super().remove()
        self.interface_state.remove()
