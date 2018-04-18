from abc import ABCMeta, abstractmethod
from .non_root_reliable import SFMRReliableState
#from typing import Union

#from .state import SFMRState
from .metric import AssertMetric as SFMRAssertMetric

#AssertStateType = Union['SFMRAssertWinner', 'SFMRAssertLooser']


class SFMRAssertImplABC(metaclass=ABCMeta):
    @abstractmethod
    def rprint(self, msg: str, *args: str) -> None:
        pass

    @abstractmethod
    def set_assert_state(self, value) -> None:
        pass

    @abstractmethod
    def get_winner_metric(self) -> SFMRAssertMetric:
        pass

    @abstractmethod
    def set_assert_winner_metric(self, value: SFMRAssertMetric) -> None:
        pass

    @abstractmethod
    def send_assert(self) -> None:
        pass

    @abstractmethod
    def send_assert_reset(self) -> None:
        pass


class SFMRAssertABC():  # pragma: no cover
    @staticmethod
    @abstractmethod
    def data_arrival(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def recv_better_metric(interface: SFMRAssertImplABC,
                           metric: SFMRAssertMetric) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def recv_worse_metric(interface, metric: SFMRAssertMetric) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def aw_failure(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def my_rpc_is_better_than_aw(interface: SFMRAssertImplABC, new_assert_metric) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def my_rpc_is_worse_than_aw(interface: SFMRAssertImplABC, new_assert_metric) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def is_now_root(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    ######################################################
    # PEDRO
    ######################################################
    @staticmethod
    @abstractmethod
    def receive_join_prune_prunel(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def receive_ack_and_info_incorrect(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def receive_ack_and_info_correct(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def timer_expires(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def is_now_assert_winner(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def is_now_assert_loser(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def last_neighbor_that_acked_is_dead(interface: SFMRAssertImplABC) -> None:
        raise NotImplemented()


class SFMRAssertWinner(SFMRAssertABC):
    @staticmethod
    def data_arrival(interface: SFMRAssertImplABC) -> None:
        #print('data_arrival, W -> W')
        interface.assert_logger.debug('data_arrival, W -> W')
        interface.send_assert()

    @staticmethod
    def recv_better_metric(interface, metric: SFMRAssertMetric) -> None:
        #print('recv_better_metric, W -> L')
        interface.assert_logger.debug('recv_better_metric, W -> L')

        interface.set_assert_state(AssertState.Looser)
        interface.set_assert_winner_metric(metric)

    @staticmethod
    def recv_worse_metric(interface, metric: SFMRAssertMetric) -> None:
        #print('recv_worse_metric, W -> W')
        interface.assert_logger.debug('recv_worse_metric, W -> W')

        interface.send_assert()

    @staticmethod
    def aw_failure(interface: SFMRAssertImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def my_rpc_is_better_than_aw(interface: SFMRAssertImplABC, new_assert_metric) -> None:
        # do nothing... im already winner
        interface.assert_logger.debug('my_rpc_is_better_than_aw, W -> W')


    @staticmethod
    def my_rpc_is_worse_than_aw(interface: SFMRAssertImplABC, new_assert_metric) -> None:
        #print('aw_rpc_worsens, W -> W')
        interface.assert_logger.debug('my_rpc_is_worse_than_aw, W -> W')

        interface.set_assert_winner_metric(new_assert_metric)
        interface.send_protected_assert()


    @staticmethod
    def is_now_root(interface: SFMRAssertImplABC) -> None:
        #print('is_now_root, W -> W')
        interface.assert_logger.debug('is_now_root, W -> W')

        interface.send_protected_assert(infinite_metric=True)

    ################################################
    # PEDRO
    ################################################
    @staticmethod
    def receive_join_prune_prunel(interface: SFMRAssertImplABC) -> None:
        interface.set_reliable_state(SFMRReliableState.UNSTABLE)

        # todo transitar para Unstable
        # save info
        # check_IT/OT
        return

    @staticmethod
    def receive_ack_and_info_incorrect(interface: SFMRAssertImplABC) -> None:
        interface.send_assert()
        # enviar Assert
        return

    @staticmethod
    def receive_ack_and_info_correct(interface: SFMRAssertImplABC) -> None:
        assert False

    @staticmethod
    def timer_expires(interface: SFMRAssertImplABC) -> None:
        have_info_from_all_neighbors = True
        for neighbor_state in interface._reliable_state_routers_dict.values():
            if neighbor_state.state == "NI" or neighbor_state.neighbor_ip != interface.get_ip() and neighbor_state.state == "AW":
                have_info_from_all_neighbors = False
                break
        if not have_info_from_all_neighbors:
            interface.set_reliable_state(SFMRReliableState.UNSTABLE, reset_timer=True)
        else:
            interface.set_reliable_state(SFMRReliableState.STABLE)

        interface.send_quack()

        # todo if some neighbors didnt answer:
        # todo      transition to unstable
        # todo else:
        # todo      transition to stable
        # todo send ACK
        return


    @staticmethod
    def is_now_assert_winner(interface: SFMRAssertImplABC) -> None:
        from .downstream_nodes_state_entry import StateEntry
        for neighbor_ip in interface._reliable_state_routers_dict.keys():
            if neighbor_ip != interface.get_ip():
                interface._reliable_state_routers_dict[neighbor_ip] = StateEntry(neighbor_ip, "NI", 0)

        # TODO LOCK CONC0RRENCIA
        interface._reliable_state_routers_dict[interface.get_ip()].state = "AW"
        interface._reliable_state_routers_dict[interface.get_ip()].counter += 1
        interface.set_reliable_state(SFMRReliableState.UNSTABLE)
        interface.send_quack()

        # todo based on saved info decide IT/OT
        # todo transition to unstable
        # todo send empty ACK and clear neighbor info
        return

    @staticmethod
    @abstractmethod
    def is_now_assert_loser(interface: SFMRAssertImplABC) -> None:
        assert False

    @staticmethod
    @abstractmethod
    def last_neighbor_that_acked_is_dead(interface: SFMRAssertImplABC) -> None:
        assert False

    def send_query_ack(self):
        # todo recolher toda a info guardada e send ACK
        return


    def __str__(self):
        return 'AW'


class SFMRAssertLooser(SFMRAssertABC):
    @staticmethod
    def data_arrival(interface: SFMRAssertImplABC) -> None:
        #print('data_arrival, L -> L')
        interface.assert_logger.debug('data_arrival, L -> L')

    @staticmethod
    def recv_better_metric(interface, metric: SFMRAssertMetric) -> None:
        #print('recv_better_metric, L -> L')
        interface.assert_logger.debug('recv_better_metric, L -> L')

        interface.set_assert_winner_metric(metric)

    @staticmethod
    def recv_worse_metric(interface, metric: SFMRAssertMetric) -> None:
        #print('recv_worse_metric, L -> W')
        interface.assert_logger.debug('recv_worse_metric, L -> W')

        interface.set_assert_state(AssertState.Winner)
        interface.set_assert_winner_metric(interface.my_rpc_metric())
        interface.send_assert()

    @staticmethod
    def aw_failure(interface: SFMRAssertImplABC) -> None:
        #print('aw_failure, L -> W')
        interface.assert_logger.debug('aw_failure, L -> W')

        interface.set_assert_state(AssertState.Winner)
        interface.set_assert_winner_metric(interface.my_rpc_metric())
        interface.send_assert()

    @staticmethod
    def my_rpc_is_better_than_aw(interface: SFMRAssertImplABC, new_assert_metric) -> None:
        # rpc better than assert winner... transition to AW
        #print('my_rpc_is_better_than_aw, L -> W')
        interface.assert_logger.debug('my_rpc_is_better_than_aw, L -> W')

        interface.set_assert_state(AssertState.Winner)
        interface.set_assert_winner_metric(interface.my_rpc_metric())
        interface.send_assert()

    @staticmethod
    def my_rpc_is_worse_than_aw(interface: SFMRAssertImplABC, new_assert_metric) -> None:
        #print('my_rpc_is_worse_than_aw, L -> L')
        interface.assert_logger.debug('my_rpc_is_worse_than_aw, L -> L')

    @staticmethod
    def is_now_root(interface: SFMRAssertImplABC) -> None:
        #print('is_now_root, L -> L')
        interface.assert_logger.debug('is_now_root, L -> L')


    ################################################
    # PEDRO
    ################################################
    @staticmethod
    def receive_join_prune_prunel(interface: SFMRAssertImplABC) -> None:
        # todo save info
        # check_IT/OT
        return

    @staticmethod
    def receive_ack_and_info_incorrect(interface: SFMRAssertImplABC) -> None:
        interface.set_reliable_state(SFMRReliableState.UNSTABLE)
        interface.send_prune_l()
        # todo transitar para unstable
        # todo enviar PruneL
        return

    @staticmethod
    def receive_ack_and_info_correct(interface: SFMRAssertImplABC) -> None:
        interface.set_reliable_state(SFMRReliableState.STABLE)
        #interface.send_prune_l()
        # todo transitar para stable
        # todo save all info that is fresher
        return

    @staticmethod
    def timer_expires(interface: SFMRAssertImplABC) -> None:
        interface.set_reliable_state(SFMRReliableState.UNSTABLE)
        interface.send_prune_l()
        # todo transition to unstable
        # todo send PruneL
        return

    @staticmethod
    @abstractmethod
    def is_now_assert_winner(interface: SFMRAssertImplABC) -> None:
        assert False

    @staticmethod
    @abstractmethod
    def is_now_assert_loser(interface: SFMRAssertImplABC) -> None:
        interface.set_reliable_state(SFMRReliableState.UNSTABLE)
        # TODO LOCK CONCORRENCIA
        interface._reliable_state_routers_dict[interface.get_ip()].state = "AL"
        interface._reliable_state_routers_dict[interface.get_ip()].counter += 1
        interface.send_prune_l()
        # todo transition to unstable
        # todo send PruneL
        return

    @staticmethod
    @abstractmethod
    def last_neighbor_that_acked_is_dead(interface: SFMRAssertImplABC) -> None:
        interface.set_reliable_state(SFMRReliableState.UNSTABLE)
        interface.send_prune_l()

        # todo transitar para AW
        # todo send empty ACK
        return

    def send_query_ack(self):
        # todo recolher toda a info guardada e send ACK
        return

    def __str__(self):
        return 'AL'

class AssertState():
    Winner = SFMRAssertWinner()
    Looser = SFMRAssertLooser()
