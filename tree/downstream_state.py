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
    def recv_tree_interest_query_1nbr(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def recv_join(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def dipt_expires(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def lost_last_nbr(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()


class SFMRDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def recv_tree_interest_query(interface: SFMRPruneImplABC) -> None:
        #print('recv_tree_interest_query, DI -> DIP')
        interface.downstream_logger.debug('recv_tree_interest_query, DI -> DIP')

        interface.set_downstream_node_interest_state(SFMRPruneState.DIP)
        interface.set_downstream_interest_pending_timer()

    @staticmethod
    def recv_tree_interest_query_1nbr(interface: SFMRPruneImplABC) -> None:
        #print('recv_tree_interest_query, DI -> NDI (only 1 nbr)')
        interface.downstream_logger.debug('recv_tree_interest_query, DI -> NDI (only 1 nbr)')

        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    @staticmethod
    def recv_join(interface: SFMRPruneImplABC) -> None:
        #print('recv_join, DI -> DI')
        interface.downstream_logger.debug('recv_join, DI -> DI')

    @staticmethod
    def dipt_expires(interface: SFMRPruneImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        #print('lost_nbr, DI -> DIP')
        interface.downstream_logger.debug('lost_nbr, DI -> DIP')

        interface.set_downstream_node_interest_state(SFMRPruneState.DIP)
        interface.set_downstream_interest_pending_timer()
        interface.send_tree_interest_query()

    @staticmethod
    def lost_last_nbr(interface: SFMRPruneImplABC) -> None:
        #print('lost_nbr, DI -> NDI')
        interface.downstream_logger.debug('lost_nbr, DI -> NDI')

        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    def __str__(self):
        return 'DI'

class SFMRDownstreamInterestedPending(SFMRDownstreamStateABC):
    @staticmethod
    def recv_tree_interest_query(interface: SFMRPruneImplABC) -> None:
        #print('recv_prune, DIP -> DIP')
        interface.downstream_logger.debug('recv_tree_interest_query, DIP -> DIP')

    @staticmethod
    def recv_tree_interest_query_1nbr(interface: SFMRPruneImplABC) -> None:
        #print('recv_prune, DIP -> NDI (only 1 nbr)')
        interface.downstream_logger.debug('recv_tree_interest_query, DIP -> NDI (only 1 nbr)')

        interface.clear_downstream_interest_pending_timer()
        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    @staticmethod
    def recv_join(interface: SFMRPruneImplABC) -> None:
        #print('recv_join, DIP -> DI')
        interface.downstream_logger.debug('recv_join, DIP -> DI')

        interface.clear_downstream_interest_pending_timer()
        interface.set_downstream_node_interest_state(SFMRPruneState.DI)

    @staticmethod
    def dipt_expires(interface: SFMRPruneImplABC) -> None:
        #print('dipt_expires, DIP -> NDI')
        interface.downstream_logger.debug('dipt_expires, DIP -> NDI')

        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    @staticmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        #print('is_now_nonroot, DIP -> DIP')
        interface.downstream_logger.debug('is_now_nonroot, DIP -> DIP')

        interface.set_downstream_interest_pending_timer()
        interface.send_tree_interest_query()

    @staticmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        #print('lost_nbr, DIP -> DIP')
        interface.downstream_logger.debug('lost_nbr, DIP -> DIP')

    @staticmethod
    def lost_last_nbr(interface: SFMRPruneImplABC) -> None:
        #print('lost_nbr (last nbr), DIP -> NDI')
        interface.downstream_logger.debug('lost_nbr (last nbr), DIP -> NDI')

        # TODO nao ha referencia acerca do DIPT mas faz sentido estar aqui
        interface.clear_downstream_interest_pending_timer()
        interface.set_downstream_node_interest_state(SFMRPruneState.NDI)

    def __str__(self):
        return 'DIP'

class SFMRNoDownstreamInterested(SFMRDownstreamStateABC):
    @staticmethod
    def recv_tree_interest_query(interface: SFMRPruneImplABC) -> None:
        #print('recv_tree_interest_query, NDI -> NDI')
        interface.downstream_logger.debug('recv_tree_interest_query, NDI -> NDI')

    @staticmethod
    def recv_tree_interest_query_1nbr(interface: SFMRPruneImplABC) -> None:
        #print('recv_tree_interest_query, NDI -> NDI')
        interface.downstream_logger.debug('recv_tree_interest_query, NDI -> NDI')

    @staticmethod
    def recv_join(interface: SFMRPruneImplABC) -> None:
        #print('recv_join, NDI -> DI')
        interface.downstream_logger.debug('recv_join, NDI -> DI')

        interface.set_downstream_node_interest_state(SFMRPruneState.DI)
        # TODO nao ha referencia acerca do DIPT e nao faz sentido estar aqui
        #interface.clear_downstream_interest_pending_timer()

    @staticmethod
    def dipt_expires(interface: SFMRPruneImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def is_now_non_root(interface: SFMRPruneImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def lost_nbr(interface: SFMRPruneImplABC) -> None:
        #print('lost_nbr, NDI -> NDI')
        interface.downstream_logger.debug('lost_nbr, NDI -> NDI')

    @staticmethod
    def lost_last_nbr(interface: SFMRPruneImplABC) -> None:
        #print('lost_nbr, NDI -> NDI')
        interface.downstream_logger.debug('lost_nbr, NDI -> NDI')

    def __str__(self):
        return 'NDI'

class SFMRPruneState():
    DI = SFMRDownstreamInterested()
    DIP = SFMRDownstreamInterestedPending()
    NDI = SFMRNoDownstreamInterested()
