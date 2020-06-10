import logging
from abc import ABCMeta, abstractmethod


class CustomFilter(logging.Filter):
    def filter(self, record):
        return record.name in ("hpim.KernelEntry", "hpim.KernelEntry.NonRootInterface.Assert", "hpim.KernelEntry.RootInterface") and \
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
        expectedState = {"R2": {"eth1": "Assert state transitions to AssertLoser"},
                         "R3": {"eth1": "Assert state transitions to AssertLoser"},
                         "R4": {"eth1": "Assert state transitions to AssertWinner"},
                         }

        success = {"R2": {"eth1": False},
                   "R3": {"eth1": False},
                   "R4": {"eth1": False},
                   }

        super().__init__("Test1", expectedState, success)

    def print_test(self):
        print("Test1: No info about (10.1.1.100,224.12.12.12) and data packets are flooded on the network")
        print("Expected: R4 AssertWinner")


class Test2(Test):
    def __init__(self):
        expectedState = {"R3": {"eth1": "Assert state transitions to AssertWinner"},
                         }

        success = {"R3": {"eth1": False},
                   }
        super().__init__("Test2", expectedState, success)

    def print_test(self):
        print("Test2: Kill Assert AssertWinner")
        print("Expected: New AssertAssertWinner will be R3")


class Test3(Test):
    def __init__(self):
        expectedState = {"R2": {"eth1": "Assert state transitions to AssertWinner"},
                         }

        success = {"R2": {"eth1": False},
                   }

        super().__init__("Test3", expectedState, success)

    def print_test(self):
        print("Test3: R3's interface eth1 becomes Root type\n" +
	      "Change interface eth0 cost of router R3 to 100, causing eth1 to be considered Root interface")
        print("Expected: New AssertAssertWinner will be R2")
