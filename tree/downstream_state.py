from abc import ABCMeta, abstractmethod

from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_downstream import TreeInterfaceDownstream


class SFMRDownstreamStateABC(metaclass=ABCMeta):
    @staticmethod
    @abstractmethod
    def in_tree(interface: 'TreeInterfaceDownstream') -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def out_tree(interface: 'TreeInterfaceDownstream') -> None:
        raise NotImplementedError()


class SFMRDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def in_tree(interface: 'TreeInterfaceDownstream') -> None:
        interface.downstream_logger.debug('DownstreamInterest -> DownstreamInterest')

    @staticmethod
    def out_tree(interface: 'TreeInterfaceDownstream') -> None:
        interface.downstream_logger.debug('DownstreamInterest -> NoDownstreamInterest')
        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    def __str__(self):
        return 'DI'


class SFMRNoDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def in_tree(interface: 'TreeInterfaceDownstream') -> None:
        interface.downstream_logger.debug('NoDownstreamInterest -> DownstreamInterest')
        interface.set_downstream_node_interest_state(SFMRPruneState.DI)

    @staticmethod
    def out_tree(interface: 'TreeInterfaceDownstream') -> None:
        interface.downstream_logger.debug('NoDownstreamInterest -> NoDownstreamInterest')

    def __str__(self):
        return 'NDI'


class SFMRPruneState():
    DI = SFMRDownstreamInterested()
    NDI = SFMRNoDownstreamInterested()
