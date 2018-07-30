import logging
from abc import ABCMeta, abstractmethod


class CustomFilter(logging.Filter):
    def filter(self, record):
        return (record.name.startswith("protocol.KernelEntry") or record.name.startswith("protocol.Interface")) and \
                record.routername in ["R1", "R2", "R3", "R4", "R5", "R6", "R7"]


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
                return False
        print('\x1b[1;32;40m' + self.testName + ' Success' + '\x1b[0m')
        return True

    @abstractmethod
    def print_test(self):
        pass


class Test1(Test):
    def __init__(self):
        expectedState = {"R1": {"eth0": "Created RootInterfaceOriginator", "eth1": "Created NonRootInterface", "eth2": "Created NonRootInterface", "eth3": "Created NonRootInterface"},
                         "R2": {"eth0": "Created RootInterface", "eth1": "Created NonRootInterface", "eth2": "Created NonRootInterface"},
                         "R3": {"eth0": "Created RootInterface", "eth1": "Created NonRootInterface"},
                         "R4": {"eth0": "Created RootInterface", "eth1": "Created NonRootInterface"},
                         "R5": {"eth0": "Created RootInterface", "eth1": "Created NonRootInterface"},
                         "R6": {"eth0": "Created RootInterface", "eth1": "Created NonRootInterface"},
                         "R7": {"eth0": "Created NonRootInterface", "eth1": "Created NonRootInterface", "eth2": "Created RootInterface"},
                         }

        success = {"R1": {"eth0": False, "eth1": False, "eth2": False, "eth3": False},
                   "R2": {"eth0": False, "eth1": False, "eth2": False},
                   "R3": {"eth0": False, "eth1": False},
                   "R4": {"eth0": False, "eth1": False},
                   "R5": {"eth0": False, "eth1": False},
                   "R6": {"eth0": False, "eth1": False},
                   "R7": {"eth0": False, "eth1": False, "eth2": False},
                   }

        super().__init__("Test1", expectedState, success)

    def print_test(self):
        print("Test1: Tree creation (10.1.1.100,224.12.12.12)")
        print("Expected: all routers should consider eth0 as their Root interface except for R7 that should consider eth2 as it Root interface")


class Test2(Test):
    def __init__(self):
        expectedState = {"R7": {"eth0": "Created RootInterface", "eth2": "Created NonRootInterface"}
                         }

        success = {"R7": {"eth0": False, "eth2": False},
                   }
        super().__init__("Test2", expectedState, success)

    def print_test(self):
        print("Test2: Change interface eth2 cost of Router R7 to 100")
        print("Expected: Router R7 should change Root<->Non-Root interface")


class Test3(Test):
    def __init__(self):
        expectedState = {"R7": {"eth0": "Created NonRootInterface", "eth2": "Created RootInterface"}
                         }

        success = {"R7": {"eth0": False, "eth2": False},
                   }
        super().__init__("Test3", expectedState, success)

    def print_test(self):
        print("Test3: Fail router 5 (disable its interfaces)")
        print("Expected: Router R7 should change Root<->Non-Root interface")
