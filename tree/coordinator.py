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


class SFMRCoordinatorStateABC(metaclass=ABCMeta):  # pragma: no cover
    @staticmethod
    @abstractmethod
    def recv_vote_interested(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def recv_vote_not_interested(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def recv_last_vote_not_interested(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def new_nbr(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def became_coordinator(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()


class SFMRIddle(SFMRCoordinatorStateABC):
    @staticmethod
    def recv_vote_interested(interface: SFMRPruneImplABC) -> None:
        interface.send_link_open()

    @staticmethod
    def recv_vote_not_interested(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRCoordinatorState.Querying)

        interface.send_tree_interest_query()

    @staticmethod
    def recv_last_vote_not_interested(interface: SFMRPruneImplABC) -> None:
        interface.send_link_pruned()

    @staticmethod
    def new_nbr(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRCoordinatorState.Querying)

        interface.send_tree_interest_query()

    @staticmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRCoordinatorState.Querying)

        interface.send_tree_interest_query()

    @staticmethod
    def became_coordinator(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRCoordinatorState.Querying)

        interface.send_tree_interest_query()

    def __str__(self):
        return 'DI'


class SFMRQuerying(SFMRCoordinatorStateABC):
    @staticmethod
    def recv_vote_interested(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRCoordinatorState.Iddle)

        interface.send_link_open()

    @staticmethod
    def recv_vote_not_interested(interface: SFMRPruneImplABC) -> None:
        return

    @staticmethod
    def recv_last_vote_not_interested(interface: SFMRPruneImplABC) -> None:
        interface.set_downstream_node_interest_state(SFMRCoordinatorState.Iddle)

        interface.send_link_pruned()

    @staticmethod
    def new_nbr(interface: SFMRPruneImplABC) -> None:
        interface.send_tree_interest_query()

    @staticmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        # TODO
        return

    @staticmethod
    def became_coordinator(interface: SFMRPruneImplABC) -> None:
        return

    def __str__(self):
        return 'NDI'

class SFMRCoordinatorState():
    Querying = SFMRQuerying()
    Iddle = SFMRIddle()
