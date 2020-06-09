#!/usr/bin/env python3

import os
import sys
import socket
import argparse
import traceback
import faulthandler
import _pickle as pickle
from hpimdm.tree import hpim_globals
from hpimdm.daemon.Daemon import Daemon
from hpimdm import Main

VERSION = "1.3.3.1"


def client_socket(data_to_send):
    """
    Send command to daemon process through a socket
    """
    # Create a UDS socket
    sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)

    # Connect the socket to the port where the server is listening
    server_address = '/tmp/hpim_uds_socket'
    #print('connecting to %s' % server_address)
    try:
        sock.connect(server_address)
        sock.sendall(pickle.dumps(data_to_send))
        data_rcv = sock.recv(1024 * 256)
        if data_rcv:
            print(pickle.loads(data_rcv))
    except socket.error:
        pass
    finally:
        #print('closing socket')
        sock.close()


class MyDaemon(Daemon):
    def run(self):
        """
        Daemon process will run this method until the daemon process explicitly is stopped
        """
        Main.main()
        server_address = '/tmp/hpim_uds_socket'

        # Make sure the socket does not already exist
        try:
            os.unlink(server_address)
        except OSError:
            if os.path.exists(server_address):
                raise

        # Create a UDS socket
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)

        # Bind the socket to the port
        sock.bind(server_address)

        # Listen for incoming connections
        sock.listen(1)
        while True:
            try:
                connection, client_address = sock.accept()
                data = connection.recv(256 * 1024)
                print(sys.stderr, 'sending data back to the client')
                print(pickle.loads(data))
                args = pickle.loads(data)
                if 'ipv4' not in args or 'ipv6' not in args or not (args.ipv4 or args.ipv6):
                    args.ipv4 = True
                    args.ipv6 = False

                if 'list_interfaces' in args and args.list_interfaces:
                    connection.sendall(pickle.dumps(Main.list_enabled_interfaces(ipv4=args.ipv4, ipv6=args.ipv6)))
                elif 'list_neighbors' in args and args.list_neighbors:
                    connection.sendall(pickle.dumps(Main.list_neighbors(ipv4=args.ipv4, ipv6=args.ipv6)))
                elif 'list_state' in args and args.list_state:
                    connection.sendall(pickle.dumps(Main.list_state(ipv4=args.ipv4, ipv6=args.ipv6)))
                elif 'list_neighbors_state' in args and args.list_neighbors_state:
                    connection.sendall(pickle.dumps(Main.list_neighbors_state(ipv4=args.ipv4, ipv6=args.ipv6)))
                elif 'list_sequence_numbers' in args and args.list_sequence_numbers:
                    connection.sendall(pickle.dumps(Main.list_sequence_numbers(ipv4=args.ipv4, ipv6=args.ipv6)))
                elif 'add_interface' in args and args.add_interface:
                    Main.add_hpim_interface(args.add_interface[0], ipv4=args.ipv4, ipv6=args.ipv6)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'flood_initial_data' in args and args.flood_initial_data:
                    connection.sendall(pickle.dumps(Main.change_initial_flood_setting()))
                elif 'hold_forwarding_state' in args and args.hold_forwarding_state:
                    connection.sendall(pickle.dumps(Main.hold_forwarding_state()))
                elif 'add_interface_igmp' in args and args.add_interface_igmp:
                    Main.add_membership_interface(interface_name=args.add_interface_igmp[0], ipv4=True, ipv6=False)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'add_interface_mld' in args and args.add_interface_mld:
                    Main.add_membership_interface(interface_name=args.add_interface_mld[0], ipv4=False, ipv6=True)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'remove_interface' in args and args.remove_interface:
                    Main.remove_interface(args.remove_interface[0], hpim=True, ipv4=args.ipv4, ipv6=args.ipv6)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'remove_interface_igmp' in args and args.remove_interface_igmp:
                    Main.remove_interface(args.remove_interface_igmp[0], membership=True, ipv4=True, ipv6=False)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'remove_interface_mld' in args and args.remove_interface_mld:
                    Main.remove_interface(args.remove_interface_mld[0], membership=True, ipv4=False, ipv6=True)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'list_hmac_algorithms' in args and args.list_hmac_algorithms:
                    connection.sendall(pickle.dumps(Main.list_hash_algorithms()))
                elif 'add_interface_security' in args and args.add_interface_security:
                    Main.add_security_key(args.add_interface_security[0], int(args.add_interface_security[1]),
                                          args.add_interface_security[2], args.add_interface_security[3],
                                          ipv4=args.ipv4, ipv6=args.ipv6)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'remove_interface_security' in args and args.remove_interface_security:
                    Main.remove_security_key(args.remove_interface_security[0], int(args.remove_interface_security[1]),
                                             ipv4=args.ipv4, ipv6=args.ipv6)
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'stop' in args and args.stop:
                    Main.stop()
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'test' in args and args.test:
                    Main.test(args.test[0], args.test[1])
                    connection.shutdown(socket.SHUT_RDWR)
                elif 'traceback' in args and args.traceback:
                    faulthandler.dump_traceback(file=sys.stderr, all_threads=True)
                    connection.shutdown(socket.SHUT_RDWR)
            except Exception:
                connection.shutdown(socket.SHUT_RDWR)
                traceback.print_exc()
            finally:
                # Clean up the connection
                connection.close()


def main():
    """
    Entry point for HPIM-DM
    """
    parser = argparse.ArgumentParser(description='HPIM-DM protocol', prog='hpim-dm')
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("-start", "--start", action="store_true", default=False,
                       help="Start Protocol")
    group.add_argument("-stop", "--stop", action="store_true", default=False,
                       help="Stop Protocol")
    group.add_argument("-restart", "--restart", action="store_true", default=False,
                       help="Restart Protocol")
    group.add_argument("-li", "--list_interfaces", action="store_true", default=False,
                       help="List All Interfaces. Use -4 or -6 to specify IPv4 or IPv6 interface.")
    group.add_argument("-ln", "--list_neighbors", action="store_true", default=False,
                       help="List All Neighbors. Use -4 or -6 to specify IPv4 or IPv6 HPIM neighbors.")
    group.add_argument("-ls", "--list_state", action="store_true", default=False,
                       help="List state of IGMP/MLD and HPIM-DM. "
                            "Use -4 or -6 to specify IPv4 or IPv6 state respectively.")
    group.add_argument("-lns", "--list_neighbors_state", action="store_true", default=False,
                       help="List Upstream and Interest state of all neighbors. "
                            "Use -4 or -6 to specify IPv4 or IPv6 HPIM neighbor state.")
    group.add_argument("-lsn", "--list_sequence_numbers", action="store_true", default=False,
                       help="List Sequence Numbers. Use -4 or -6 to list stored IPv4 or IPv6 HPIM sequence numbers.")
    group.add_argument("-mr", "--multicast_routes", action="store_true", default=False,
                       help="List Multicast Routing table. "
                            "Use -4 or -6 to specify IPv4 or IPv6 multicast routing table.")
    group.add_argument("-fid", "--flood_initial_data", action="store_true", default=False,
                       help="Flood initial data packets")
    group.add_argument("-hfs", "--hold_forwarding_state", action="store_true", default=False,
                       help="Hold forwarding state during a small amount of time after AW interface becomes AL " +
                            "(prevent loss of data packets after AW replacement)")
    group.add_argument("-ai", "--add_interface", nargs=1, metavar='INTERFACE_NAME',
                       help="Add HPIM-DM interface. Use -4 or -6 to specify IPv4 or IPv6 interface.")
    group.add_argument("-aiigmp", "--add_interface_igmp", nargs=1, metavar='INTERFACE_NAME',
                       help="Add IGMP interface")
    group.add_argument("-aimld", "--add_interface_mld", nargs=1, metavar='INTERFACE_NAME',
                       help="Add MLD interface")
    group.add_argument("-ri", "--remove_interface", nargs=1, metavar='INTERFACE_NAME',
                       help="Remove HPIM-DM interface. Use -4 or -6 to specify IPv4 or IPv6 interface.")
    group.add_argument("-riigmp", "--remove_interface_igmp", nargs=1, metavar='INTERFACE_NAME',
                       help="Remove IGMP interface")
    group.add_argument("-rimld", "--remove_interface_mld", nargs=1, metavar='INTERFACE_NAME',
                       help="Remove MLD interface")
    group.add_argument("-lsec", "--list_hmac_algorithms", action="store_true", default=False,
                       help="List available HMAC Hash algorithms")
    group.add_argument("-aisec", "--add_interface_security", nargs=4, metavar=('INTERFACE_NAME', "SECURITY_IDENTIFIER",
                                                                               "HASH_FUNCTION", "KEY"),
                       help="Add security information to interface INTERFACE_NAME. Control messages will be secured " +
                            " with SECURITY_IDENTIFIER, HMAC algorithm based on HASH_FUNCTION and key KEY. " +
                            "Use -4 or -6 to specify IPv4 or IPv6 HPIM interface. " +
                            "To determine available hash functions run -lsec command")
    group.add_argument("-risec", "--remove_interface_security", nargs=2, metavar=('INTERFACE_NAME',
                                                                                  "SECURITY_IDENTIFIER"),
                       help="Remove security information identified by SECURITY_IDENTIFIER from interface INTERFACE_NAME."
                            " Use -4 or -6 to specify IPv4 or IPv6 interface.")
    group.add_argument("-v", "--verbose", action="store_true", default=False,
                       help="Verbose (print all debug messages)")
    group.add_argument("-t", "--test", nargs=2, metavar=('ROUTER_NAME', 'SERVER_LOG_IP'),
                       help="Tester... send log information to SERVER_LOG_IP. Set the router name to ROUTER_NAME")
    group.add_argument("-traceback", "--traceback", action="store_true", default=False,
                       help="Dump the tracebacks of all threads into file")
    group.add_argument("--version", action='version', version='%(prog)s ' + VERSION)
    group_ipversion = parser.add_mutually_exclusive_group(required=False)
    group_ipversion.add_argument("-4", "--ipv4", action="store_true", default=False, help="Setting for IPv4")
    group_ipversion.add_argument("-6", "--ipv6", action="store_true", default=False, help="Setting for IPv6")
    args = parser.parse_args()

    #print(parser.parse_args())
    # This script must be run as root!
    if os.geteuid() != 0:
        sys.exit('HPIM-DM must be run as root!')

    daemon = MyDaemon('/tmp/Daemon-hpim.pid')
    if args.start:
        print("start")
        daemon.start()
        sys.exit(0)
    elif args.stop:
        client_socket(args)
        daemon.stop()
        sys.exit(0)
    elif args.restart:
        daemon.restart()
        sys.exit(0)
    elif args.verbose:
        os.system("tail -f /var/log/hpimdm/stdout")
        sys.exit(0)
    elif args.multicast_routes:
        if args.ipv4 or not args.ipv6:
            os.system("ip mroute show table " + str(hpim_globals.MULTICAST_TABLE_ID))
        elif args.ipv6:
            os.system("ip -6 mroute show table " + str(hpim_globals.MULTICAST_TABLE_ID))
        sys.exit(0)
    elif not daemon.is_running():
        print("HPIM-DM is not running")
        parser.print_usage()
        sys.exit(0)

    client_socket(args)


if __name__ == "__main__":
    main()
