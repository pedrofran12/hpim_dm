import logging
from abc import ABCMeta, abstractmethod


class CustomFilter(logging.Filter):
    def filter(self, record):
        return record.name in ("protocol.Interface.Neighbor", "protocol.Interface") and \
                record.routername in ["R1", "R2"]


class Test(object):
    __metaclass__ = ABCMeta

    def __init__(self, testName, expectedState, success):
        self.testName = testName
        self.expectedState = expectedState
        self.success = success

    def test(self, record):
        if record.routername not in self.expectedState:
            return False
        if record.msg.startswith(self.expectedState.get(record.routername).get(record.interfacename)):
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


class Test1(Test):
    def __init__(self):
        expectedState = {"R1": {"eth0": "Neighbor state of 10.0.0.2 transitions to Synced"},
                         "R2": {"eth0": "Neighbor state of 10.0.0.1 transitions to Synced"},
                         }

        success = {"R1": {"eth0": False},
                   "R2": {"eth0": False},
                   }

        super().__init__("Test1", expectedState, success)

    def print_test(self):
        print("Test1: Neighborhood relationships")
        print("Start R1 and R2.... they should transition to Synced state")


class Test2(Test):
    def __init__(self):
        expectedState = {"R1": {"eth0": "Neighbor state of 10.0.0.2 transitions to Synced"},
                         "R2": {"eth0": "Neighbor state of 10.0.0.1 transitions to Synced"},
                         }

        success = {"R1": {"eth0": False},
                   "R2": {"eth0": False},
                  }
        super().__init__("Test2", expectedState, success)

    def print_test(self):
        print("Test2: Restart R2")
        print("Synchronization should be restarted and both at the end must be in Synced state")


class Test3(Test):
    def __init__(self):
        expectedState = {"R1": {"eth0": "Removing neighbor 10.0.0.2"},
                         }

        success = {"R1": {"eth0": False},
                   }

        super().__init__("Test3", expectedState, success)

    def print_test(self):
        print("Test3: Neighbor failure should be detected")
        print("Fail R2... R1 should transition R2 to Unknown state, due to the absence of Hello messages")
