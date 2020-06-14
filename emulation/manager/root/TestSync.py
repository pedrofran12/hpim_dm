import logging
import socket
import time
import traceback
from abc import ABCMeta, abstractmethod


ROUTER_PORT = 12000
ROUTER1_IP = '172.16.1.1'
ROUTER2_IP = '172.16.1.2'
ROUTER3_IP = '172.16.1.3'
ROUTER4_IP = '172.16.1.4'
ROUTER5_IP = '172.16.1.5'
ROUTER6_IP = '172.16.1.6'
ROUTER7_IP = '172.16.1.7'
SOURCE_IP = '172.16.1.8'
CLIENT0_IP = '172.16.1.9'
CLIENT1_IP = '172.16.1.10'
MANAGER_IP = '172.16.1.100'

ROUTER1_NAME = "R1"
ROUTER2_NAME = "R2"
ROUTER3_NAME = "R3"
ROUTER4_NAME = "R4"
ROUTER5_NAME = "R5"
ROUTER6_NAME = "R6"
ROUTER7_NAME = "R7"
SOURCE_NAME = "SOURCE"
CLIENT0_NAME = "CLIENT0"
CLIENT1_NAME = "CLIENT1"


class CustomFilter(logging.Filter):
    def filter(self, record):
        return record.name in ("hpim.Interface.Neighbor", "hpim.Interface", "tests") and \
                record.routername in ["R2", "R3", "R4", "R5", "R6"]


class Test(object):
    __metaclass__ = ABCMeta

    def __init__(self, testName, expectedState, success):
        self.testName = testName
        self.expectedState = expectedState
        self.success = success

    def test(self, record):
        if record.routername not in self.expectedState:
            return False
        if record.msg.startswith(self.expectedState.get(record.routername).get(record.interfacename, "InterfaceNotExistent")):
            self.success[record.routername][record.interfacename] = True

        for interface_test in self.success.values():
            if False in interface_test.values():
                return False
        print('\x1b[1;32;40m' + self.testName + ' Success' + '\x1b[0m')
        return True

    @abstractmethod
    def print_test(self):
        pass

    @abstractmethod
    def set_router_state(self):
        pass

    @staticmethod
    def set_initial_settings():
        # format = client_name. client_ip, server_ip
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

        msg = "set R1 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER1_IP, ROUTER_PORT))

        msg = "set R2 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER2_IP, ROUTER_PORT))

        msg = "set R3 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER3_IP, ROUTER_PORT))

        msg = "set R4 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER4_IP, ROUTER_PORT))

        msg = "set R5 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER5_IP, ROUTER_PORT))

        msg = "set R6 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER6_IP, ROUTER_PORT))

        msg = "set R7 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (ROUTER7_IP, ROUTER_PORT))

        msg = "set SOURCE {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (SOURCE_IP, ROUTER_PORT))

    @staticmethod
    def stop_everything():
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER1_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER2_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER3_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER4_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER5_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER6_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER7_IP, ROUTER_PORT))

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (SOURCE_IP, ROUTER_PORT))


class Test1(Test):
    def __init__(self):
        expectedState = {"R2": {"eth1": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         "R3": {"eth1": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         "R5": {"eth0": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         "R6": {"eth0": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         }

        success = {"R2": {"eth1": False},
                   "R3": {"eth1": False},
                   "R5": {"eth0": False},
                   "R6": {"eth0": False},
                   }

        super().__init__("Test1", expectedState, success)

    def print_test(self):
        print("Test1: Start all routers")
        print("All routers must establish neighborhood relationships with each other")

    def set_router_state(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # INITIAL STATE ROUTER 1
            router_ip = ROUTER1_IP
            router_name = ROUTER1_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth2"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth2"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth3"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth3"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            # INITIAL STATE ROUTER 2
            router_ip = ROUTER2_IP
            router_name = ROUTER2_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth2"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth2"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            # INITIAL STATE ROUTER 3
            router_ip = ROUTER3_IP
            router_name = ROUTER3_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            # INITIAL STATE ROUTER 4
            router_ip = ROUTER4_IP
            router_name = ROUTER4_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            # INITIAL STATE ROUTER 5
            router_ip = ROUTER5_IP
            router_name = ROUTER5_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            # INITIAL STATE ROUTER 6
            router_ip = ROUTER6_IP
            router_name = ROUTER6_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            # INITIAL STATE ROUTER 7
            router_ip = ROUTER7_IP
            router_name = ROUTER7_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "t {} {}".format(router_name, MANAGER_IP)
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth2"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "aiigmp eth2"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
        except:
            print(traceback.format_exc())


class Test2(Test):
    def __init__(self):
        expectedState = {"R2": {"eth1": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         "R3": {"eth1": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         "R5": {"eth0": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         "R6": {"eth0": "Neighbor state of 10.5.5.4 transitions to Synced"},
                         }

        success = {"R2": {"eth1": False},
                   "R3": {"eth1": False},
                   "R5": {"eth0": False},
                   "R6": {"eth0": False},
                   }

        super().__init__("Test2", expectedState, success)

    def print_test(self):
        print("Test2: Create all trees and reboot interface eth1 of current Assert Winner (R4)")
        print("All routers must establish establish neighborhood relationships with the rebooted router... The rebooted router must include the tree in Sync messages")

    def set_router_state(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # INITIAL STATE SOURCE
            router_ip = SOURCE_IP
            router_name = SOURCE_NAME
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            time.sleep(20)

            # INITIAL STATE ROUTER 4
            router_ip = ROUTER4_IP
            router_name = ROUTER4_NAME
            msg = "ri eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth1"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
        except:
            pass


class Test3(Test):
    def __init__(self):
        expectedState = {"R2": {"eth1": "Neighbor state of 10.5.5.5 transitions to Synced"},
                         "R3": {"eth1": "Neighbor state of 10.5.5.5 transitions to Synced"},
                         "R4": {"eth1": "Neighbor state of 10.5.5.5 transitions to Synced"},
                         "R6": {"eth0": "Neighbor state of 10.5.5.5 transitions to Synced"},
                         }

        success = {"R2": {"eth1": False},
                   "R3": {"eth1": False},
                   "R4": {"eth1": False},
                   "R6": {"eth0": False},
                   }

        super().__init__("Test3", expectedState, success)

    def print_test(self):
        print("Test3: Reboot Non-Upstream router R5")
        print("All routers must establish establish neighborhood relationships with the rebooted router.... This router must not include the tree in the Sync messages because it is connected by a Root interface to the link")

    def set_router_state(self):
        # INITIAL STATE ROUTER 4
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            router_ip = ROUTER5_IP
            router_name = ROUTER5_NAME
            msg = "ri eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
            msg = "ai eth0"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
        except:
            pass
