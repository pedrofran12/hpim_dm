import logging
import socket
import traceback
import time
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
        return record.name in ("hpim.KernelEntry.NonRootInterface.Downstream", "hpim.Interface", "tests") and \
                record.routername in ["R1", "R2", "R3", "R4", "R5", "R6", "R7", "CLIENT0", "CLIENT1", "SOURCE"]


class Test(object):
    __metaclass__ = ABCMeta

    def __init__(self, testName, expectedState, success):
        self.testName = testName
        self.expectedState = expectedState
        self.success = success

    def test(self, record):
        if record.routername not in self.expectedState:
            return False
        if record.msg == self.expectedState.get(record.routername).get(record.interfacename):
            self.success[record.routername][record.interfacename] = True

        for interface_test in self.success.values():
            if False in interface_test.values():
                #print(self.expectedState)
                #print(self.success)
                return False
        print('\x1b[1;32;40m' + self.testName + ' Success' + '\x1b[0m')
        return True

    @abstractmethod
    def print_test(self):
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

        msg = "set CLIENT0 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (CLIENT0_IP, ROUTER_PORT))

        msg = "set CLIENT1 {}".format(MANAGER_IP)
        sock.sendto(msg.encode('utf-8'), (CLIENT1_IP, ROUTER_PORT))

    @staticmethod
    def stop_everything():
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)

        msg = "stop"
        sock.sendto(msg.encode('utf-8'), (ROUTER1_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (ROUTER2_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (ROUTER3_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (ROUTER4_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (ROUTER5_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (ROUTER6_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (ROUTER7_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (SOURCE_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (CLIENT0_IP, ROUTER_PORT))
        sock.sendto(msg.encode('utf-8'), (CLIENT1_IP, ROUTER_PORT))


class Test1(Test):
    def __init__(self):
        expectedState = {"R1": {"eth1": "Downstream interest state transitions to NoDownstreamInterest",
                                "eth2": "Downstream interest state transitions to NoDownstreamInterest",
                                "eth3": "Downstream interest state transitions to DownstreamInterest"},
                         "R2": {"eth2": "Downstream interest state transitions to NoDownstreamInterest"},
                         "R4": {"eth1": "Downstream interest state transitions to DownstreamInterest"},
                         "R5": {"eth1": "Downstream interest state transitions to DownstreamInterest"},
                         "R7": {"eth2": "Downstream interest state transitions to NoDownstreamInterest"},
                         }

        success = {"R1": {"eth1": False, "eth2": False, "eth3": False},
                   "R2": {"eth2": False},
                   "R4": {"eth1": False},
                   "R5": {"eth1": False},
                   "R7": {"eth2": False},
                   }

        super().__init__("Test1", expectedState, success)

    def print_test(self):
        print("Test1: Formation of (S,G) Broadcast Tree")
        print("Having Client0 and Client1 interested")

    def set_router_state(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # INITIAL STATE CLIENT0
            router_ip = CLIENT0_IP
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            router_ip = CLIENT1_IP
            msg = "start"
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

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

            # give time for routers to synchronize
            # and start source
            time.sleep(10)
            msg = "start"
            router_ip = SOURCE_IP
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
        except:
            print(traceback.format_exc())


class Test2(Test):
    def __init__(self):
        expectedState = {"R1": {"eth3": "Downstream interest state transitions to NoDownstreamInterest"},
                         "R4": {"eth1": "Downstream interest state transitions to NoDownstreamInterest"},
                         "R5": {"eth1": "Downstream interest state transitions to NoDownstreamInterest"},
                         }

        success = {"R1": {"eth3": False},
                   "R4": {"eth1": False},
                   "R5": {"eth1": False},
                   }
        super().__init__("Test2", expectedState, success)

    def print_test(self):
        print("Test2: Start by having Client1 not interested in receiving traffic destined to group G, then have Client0 also not interested in that traffic")
        print("R6 must send a NoInterest, but traffic should continue be forwarded by R4 (due to the interest message of R5)")
        print("Then stop having Client0 interested.... Router R5 must send a NoInterest... This last message must cause R4 to stop having interested downstream routers connected to its NonRoot interface")
        print("Expected: After both clients stop having interest this should cause R1 and R4 to not have downstream clients interested... causing a prune of the tree")

    def set_router_state(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # CAUSE NO INTEREST OF CLIENT1
            msg = "stop"
            router_ip = CLIENT1_IP
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            time.sleep(10)

            # CAUSE NO INTEREST OF CLIENT0
            msg = "stop"
            router_ip = CLIENT0_IP
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
        except:
            print(traceback.format_exc())


class Test3(Test):
    def __init__(self):
        expectedState = {"R1": {"eth3": "Downstream interest state transitions to DownstreamInterest"},
                         "R4": {"eth1": "Downstream interest state transitions to DownstreamInterest"},
                         }

        success = {"R1": {"eth3": False},
                   "R4": {"eth1": False},
                   }

        super().__init__("Test3", expectedState, success)

    def print_test(self):
        print("Test3: Have client1 interested again in multicast traffic")
        print("Expected: R1 and R4 should consider that there is downstream interest in this traffic, causing the \"graft\" of the tree")

    def set_router_state(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # CAUSE INTEREST OF CLIENT1
            msg = "start"
            router_ip = CLIENT1_IP
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))

            time.sleep(10)
        except:
            print(traceback.format_exc())

class Test4(Test):
    def __init__(self):
        expectedState = {"R5": {"eth1": "Downstream interest state transitions to DownstreamInterest"},
                         }

        success = {"R5": {"eth1": False},
                   }

        super().__init__("Test4", expectedState, success)

    def print_test(self):
        print("Test4: Have client0 interested again in multicast traffic")
        print("Expected: R5 should consider that there is downstream interest in this traffic, causing the \"graft\" of the link that connects R7 to R5")

    def set_router_state(self):
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            # CAUSE INTEREST OF CLIENT0
            msg = "start"
            router_ip = CLIENT0_IP
            sock.sendto(msg.encode('utf-8'), (router_ip, ROUTER_PORT))
        except:
            print(traceback.format_exc())
