from abc import ABCMeta, abstractmethod
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

    def __str__(self):
        return 'AL'

class AssertState():
    Winner = SFMRAssertWinner()
    Looser = SFMRAssertLooser()
