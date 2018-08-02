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
        return True

    def __str__(self):
        return 'DownstreamInterest'


class SFMRNoDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def are_downstream_nodes_interested():
        return False

    def __str__(self):
        return 'NoDownstreamInterest'


class SFMRPruneState():
    DI = SFMRDownstreamInterested()
    NDI = SFMRNoDownstreamInterested()
