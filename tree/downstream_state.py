from abc import ABCMeta, abstractmethod

from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_downstream import TreeInterfaceDownstream


class SFMRDownstreamStateABC(metaclass=ABCMeta):
    @staticmethod
    @abstractmethod
    def are_downstream_nodes_interested() -> bool:
        raise NotImplementedError()

class SFMRDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def are_downstream_nodes_interested():
        """
        Determine if this state considers downstream nodes to be Interested in receiving data packets
        """
        return True

    def __str__(self):
        return 'DownstreamInterest'


class SFMRNoDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def are_downstream_nodes_interested():
        """
        Determine if this state considers downstream nodes to be Interested in receiving data packets
        """
        return False

    def __str__(self):
        return 'NoDownstreamInterest'


class SFMRPruneState():
    DI = SFMRDownstreamInterested()
    NDI = SFMRNoDownstreamInterested()
