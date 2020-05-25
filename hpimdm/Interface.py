import socket
import struct
import threading
import netifaces
import ipaddress
import traceback
from fcntl import ioctl
from abc import ABCMeta, abstractmethod

SIOCGIFMTU = 0x8921


class Interface(metaclass=ABCMeta):
    MCAST_GRP = '224.0.0.13'

    def __init__(self, interface_name, recv_socket, send_socket, vif_index):
        self.interface_name = interface_name

        # virtual interface index for the multicast routing table
        self.vif_index = vif_index

        # set receive socket and send socket
        self._send_socket = send_socket
        self._recv_socket = recv_socket
        self.interface_enabled = False

    def enable(self):
        """
        Enable this interface
        This will start a thread to be executed in the background to be used in the reception of control packets
        """
        self.interface_enabled = True
        # run receive method in background
        receive_thread = threading.Thread(target=self.receive)
        receive_thread.daemon = True
        receive_thread.start()

    def receive(self):
        """
        Method that will be executed in the background for the reception of control packets
        """
        while self.interface_enabled:
            try:
                (raw_bytes, ancdata, _, src_addr) = self._recv_socket.recvmsg(256 * 1024, 500)
                if raw_bytes:
                    self._receive(raw_bytes, ancdata, src_addr)
            except Exception:
                traceback.print_exc()
                continue

    @abstractmethod
    def _receive(self, raw_bytes, ancdata, src_addr):
        """
        Subclass method to be implemented
        This method will be invoked whenever a new control packet is received
        """
        raise NotImplementedError

    def send(self, data: bytes, group_ip: str):
        """
        Send a control packet through this interface
        Explicitly destined to group_ip (can be unicast or multicast IP)
        """
        if self.interface_enabled and data:
            try:
                self._send_socket.sendto(data, (group_ip, 0))
            except socket.error:
                pass

    def remove(self):
        """
        This interface is no longer active....
        Clear all state regarding it
        """
        self.interface_enabled = False
        try:
            self._recv_socket.shutdown(socket.SHUT_RDWR)
        except Exception:
            pass
        self._recv_socket.close()
        self._send_socket.close()

    def is_enabled(self):
        """
        Verify if this interface is enabled
        """
        return self.interface_enabled

    @abstractmethod
    def get_ip(self):
        """
        Get IP of this interface
        """
        raise NotImplementedError

    def get_all_interface_networks(self):
        """
        Get all subnets associated with this interface.
        Used to verify if interface is directly connected to a multicast source
        This is extremely relevant on IPv6, where an interface can be connected to multiple subnets (global, link-local,
        unique-local)
        """
        all_networks = set()
        for if_addr in netifaces.ifaddresses(self.interface_name)[self._get_address_family()]:
            ip_addr = if_addr["addr"].split("%")[0]
            netmask = if_addr["netmask"].split("/")[0]
            prefix_length = str(bin(int(ipaddress.ip_address(netmask).packed.hex(), 16)).count('1'))
            network = ip_addr + "/" + prefix_length
            all_networks.add(str(ipaddress.ip_interface(network).network))
        return all_networks

    @staticmethod
    @abstractmethod
    def _get_address_family():
        raise NotImplementedError

    def get_mtu(self):
        """
        Get MTU of this interface
        """
        '''Use socket ioctl call to get MTU size'''
        s = socket.socket(type=socket.SOCK_DGRAM)
        ifr = self.interface_name + '\x00'*(32-len(self.interface_name))
        try:
            ifs = ioctl(s, SIOCGIFMTU, ifr)
            mtu = struct.unpack('<H', ifs[16:18])[0]
        except:
            traceback.print_exc()
            raise

        #log.debug('get_mtu: mtu of {0} = {1}'.format(self.ifname, mtu))
        return mtu
