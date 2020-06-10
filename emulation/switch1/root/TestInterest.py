import logging
from abc import ABCMeta, abstractmethod


class CustomFilter(logging.Filter):
    def filter(self, record):
        return record.name in ("hpim.KernelEntry.NonRootInterface.Downstream", "hpim.Interface") and \
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
