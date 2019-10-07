import logging
from abc import ABCMeta, abstractmethod


class CustomFilter(logging.Filter):
    def filter(self, record):
        return record.name in ("protocol.Interface.Neighbor", "protocol.Interface") and \
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
