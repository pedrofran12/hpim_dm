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


class SFMRReliableStateABC(metaclass=ABCMeta):
    @staticmethod
    @abstractmethod
    def receive_RECENT_join_prune_prunel(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def receive_ack_and_info_correct(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def receive_ack_and_info_incorrect_or_not_existent(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def timer_expires(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def transition_to_assert_winner(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def transition_to_assert_loser(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()

    @staticmethod
    @abstractmethod
    def last_neighbor_that_acked_is_dead(interface: SFMRPruneImplABC) -> None:
        raise NotImplementedError()



class SFMRStable(SFMRReliableStateABC):
    @staticmethod
    def receive_RECENT_join_prune_prunel(interface: SFMRPruneImplABC) -> None:
        # todo save info
        interface._assert_state.receive_join_prune_prunel(interface)

    @staticmethod
    def receive_ack_and_info_correct(interface: SFMRPruneImplABC) -> None:
        # todo save recent info
        interface._assert_state.receive_ack_and_info_correct(interface)

    @staticmethod
    def receive_ack_and_info_incorrect_or_not_existent(interface: SFMRPruneImplABC) -> None:
        # todo save recent info
        interface._assert_state.receive_ack_and_info_incorrect(interface)

    @staticmethod
    def timer_expires(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.timer_expires(interface)

    @staticmethod
    def transition_to_assert_winner(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.is_now_assert_winner(interface)


    @staticmethod
    def transition_to_assert_loser(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.is_now_assert_loser(interface)


    @staticmethod
    def last_neighbor_that_acked_is_dead(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.last_neighbor_that_acked_is_dead(interface)


    @staticmethod
    def transition(interface: SFMRPruneImplABC) -> None:
        interface.clear_reliable_timer()



    '''
    @staticmethod
    def receive_ack_and_info_correct(interface: SFMRPruneImplABC) -> None:
        #todo guardar ip do neighor q fez ack
        return

    @staticmethod
    def receive_ack_and_info_incorrect_or_not_existent(interface: SFMRPruneImplABC) -> None:
        # todo transitar para unstable
        # todo enviar join/prune
        # todo start timer
        return

    @staticmethod
    def timer_expires(interface: SFMRPruneImplABC) -> None:
        return

    @staticmethod
    def last_neighbor_that_correctly_acked_died(interface: SFMRPruneImplABC) -> None:
        # todo transitar para unstable
        # todo enviar join/prune
        # todo start timer
        return
    '''
    def __str__(self):
        return 'Stable'


class SFMRUnstable(SFMRReliableStateABC):
    @staticmethod
    def receive_RECENT_join_prune_prunel(interface: SFMRPruneImplABC) -> None:
        # todo save info
        interface._assert_state.receive_join_prune_prunel(interface)

    @staticmethod
    def receive_ack_and_info_correct(interface: SFMRPruneImplABC) -> None:
        # todo save recent info
        interface._assert_state.receive_ack_and_info_correct(interface)

    @staticmethod
    def receive_ack_and_info_incorrect_or_not_existent(interface: SFMRPruneImplABC) -> None:
        # todo save recent info
        interface._assert_state.receive_ack_and_info_incorrect(interface)

    @staticmethod
    def timer_expires(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.timer_expires(interface)

    @staticmethod
    def transition_to_assert_winner(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.is_now_assert_winner(interface)

    @staticmethod
    def transition_to_assert_loser(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.is_now_assert_loser(interface)

    @staticmethod
    def last_neighbor_that_acked_is_dead(interface: SFMRPruneImplABC) -> None:
        interface._assert_state.last_neighbor_that_acked_is_dead(interface)

    @staticmethod
    def transition(interface: SFMRPruneImplABC) -> None:
        interface.set_reliable_timer()
    '''
    @staticmethod
    def in_tree(interface: SFMRPruneImplABC) -> None:
        interface.downstream_logger.debug('IT, NDI -> DI')
        interface.set_downstream_node_interest_state(SFMRPruneState.DI)

    @staticmethod
    def out_tree(interface: SFMRPruneImplABC) -> None:
        interface.downstream_logger.debug('OT, NDI -> NDI')
    
    @staticmethod
    def receive_ack_and_info_correct(interface: SFMRPruneImplABC) -> None:
        # todo transitar para stable
        # todo clear timer
        # todo guardar ip do neighbor q fez ack
        return

    @staticmethod
    def receive_ack_and_info_incorrect_or_not_existent(interface: SFMRPruneImplABC) -> None:
        # todo enviar join/prune
        # todo reset timer
        return

    @staticmethod
    def timer_expires(interface: SFMRPruneImplABC) -> None:
        # todo enviar join/prune
        # todo reset timer
        return

    @staticmethod
    def last_neighbor_that_correctly_acked_died(interface: SFMRPruneImplABC) -> None:
        return
    '''


class SFMRReliableState():
    STABLE = SFMRStable()
    UNSTABLE = SFMRUnstable()
