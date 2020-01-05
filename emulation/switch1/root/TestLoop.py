import logging
from abc import ABCMeta, abstractmethod


class CustomFilter(logging.Filter):
    def filter(self, record):
        return record.name in ("protocol.KernelEntry", "protocol.KernelEntryOriginator", "protocol.Interface", "protocol.KernelEntry.RootInterface") and \
                record.routername in ["R1", "R2", "R3", "R4", "R5"]


class Test(object):
    __metaclass__ = ABCMeta

    def __init__(self, testName, expectedState, success):
        self.testName = testName
        self.expectedState = expectedState
        self.success = success

    def test(self, record):
        if record.routername not in self.expectedState:
            return False
        if record.msg == self.expectedState.get(record.routername):
            self.success[record.routername] = True

        if False in self.success.values():
            return False
        print('\x1b[1;32;40m' + self.testName + ' Success' + '\x1b[0m')
        return True

    @abstractmethod
    def print_test(self):
        pass


class Test1(Test):
    def __init__(self):
        expectedState = {"R1": "Tree transitions to Active",
                         "R2": "Tree transitions to Active",
                         "R3": "Tree transitions to Active",
                         "R4": "Tree transitions to Active",
                         "R5": "Tree transitions to Active",
                         }

        success = {"R1": False,
                   "R2": False,
                   "R3": False,
                   "R4": False,
                   "R5": False,
                   }

        super().__init__("Test1", expectedState, success)

    def print_test(self):
        print("Test1: Create tree (10.1.1.100,224.12.12.12) by transmitting data packets from Source")
        print("Expected: All routers must consider the tree to be Active")


class Test2(Test):
    def __init__(self):
        expectedState = {"R1": "Tree transitions to Inactive",
                         "R2": "Tree transitions to Inactive",
                         "R3": "Tree transitions to Inactive",
                         "R4": "Tree transitions to Inactive",
                         "R5": "Tree transitions to Inactive",
                         }

        success = {"R1": False,
                   "R2": False,
                   "R3": False,
                   "R4": False,
                   "R5": False,
                   }
        super().__init__("Test2", expectedState, success)

    def print_test(self):
        print("Test2: Stop transmitting data packets from Source")
        print("Expected: Eventually all routers must transition the tree to state Inactive")
