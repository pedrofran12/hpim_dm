from abc import ABCMeta, abstractmethod
#from typing import Union


#SFMRPruneStateType = Union['SFMRNoInfo', 'SFMRDownstreamInterested',
#                           'SFMRDownstreamInterestedPending',
#                           'SFMRNoDownstreamInterested', ]


class SFMRPruneImplABC(metaclass=ABCMeta):
    @abstractmethod
    def rprint(self, msg: str, *args: str) -> None:
        pass

    @abstractmethod
    def set_downstream_node_interest_state(self, state: 'SFMRPruneStateType') -> None:
        pass

    @abstractmethod
    def set_downstream_interest_pending_timer(self):
        pass

    @abstractmethod
    def clear_downstream_interest_pending_timer(self):
        pass

    @abstractmethod
    def send_tree_interest_query(self) -> None:
        pass


class SFMRDownstreamStateABC(metaclass=ABCMeta):  # pragma: no cover
    @staticmethod
    @abstractmethod
    def recv_tree_interest_query(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def recv_link_open(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def recv_link_pruned(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def has_no_neighbors(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()


class SFMRDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def recv_tree_interest_query(interface: SFMRPruneImplABC) -> None:
        #print('recv_tree_interest_query, DI -> DIP')
        interface.downstream_logger.debug('recv_tree_interest_query, DI -> DIP')
        interface.send_vote_not_interested()

    @staticmethod
    def recv_link_open(interface: SFMRPruneImplABC) -> None:
        return

    @staticmethod
    def recv_link_pruned(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    @staticmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        interface.send_vote_not_interested()

    @staticmethod
    def has_no_neighbors(interface: SFMRPruneImplABC) -> None:
        interface.downstream_logger.debug('lost_nbr, DI -> DIP')

        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    def __str__(self):
        return 'DI'


class SFMRNoDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def recv_tree_interest_query(interface: SFMRPruneImplABC) -> None:
        interface.downstream_logger.debug('recv_tree_interest_query, NDI -> NDI')
        interface.send_vote_not_interested()

    @staticmethod
    def recv_link_open(interface: SFMRPruneImplABC) -> None:
        interface.downstream_logger.debug('recv_join, NDI -> DI')
        interface.set_downstream_node_interest_state(SFMRPruneState.DI)

    @staticmethod
    def recv_link_pruned(interface: SFMRPruneImplABC) -> None:
        return

    @staticmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        assert False

    @staticmethod
    def has_no_neighbors(interface: SFMRPruneImplABC) -> None:
        return

    def __str__(self):
        return 'NDI'

class SFMRPruneState():
    DI = SFMRDownstreamInterested()
    NDI = SFMRNoDownstreamInterested()
