from abc import ABC, abstractmethod
from typing import Union


class SFMROriginatorABC():  # pragma: no cover
    @staticmethod
    @abstractmethod
    def data_arrival_from_directly_attached_source(interface) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def sat_expires(interface) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def recv_confirm(interface) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def recv_remove_tree(interface) -> None:
        raise NotImplemented()

    @staticmethod
    @abstractmethod
    def recv_set_tree(interface) -> None:
        raise NotImplemented()


class SFMRAssertWinner(SFMRAssertABC):
    @staticmethod
    def data_arrival(interface: SFMRAssertImplABC) -> None:
        print('data_arrival, W -> W')
        interface.send_assert()

    @staticmethod
    def recv_better_metric(interface, metric: SFMRAssertMetric) -> None:
        print('recv_better_metric, W -> L')

        interface.set_assert_state(AssertState.Looser)
        interface.set_winner_metric(metric)

    @staticmethod
    def recv_worse_metric(interface, metric: SFMRAssertMetric) -> None:
        print('recv_worse_metric, W -> W')

        interface.send_assert()

    @staticmethod
    def aw_failure(interface: SFMRAssertImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def al_rpc_better_than_aw(interface: SFMRAssertImplABC) -> None:
        assert False  # pragma: no cover

    @staticmethod
    def aw_rpc_worsens(interface: SFMRAssertImplABC) -> None:
        print('aw_rpc_worsens, W -> W')

        interface.send_assert_reset()

class SFMRAssertLooser(SFMRAssertABC):
    @staticmethod
    def data_arrival(interface: SFMRAssertImplABC) -> None:
        print('data_arrival, L -> L')

    @staticmethod
    def recv_better_metric(interface, metric: SFMRAssertMetric) -> None:
        print('recv_better_metric, L -> L')

        interface.set_winner_metric(metric)

    @staticmethod
    def recv_worse_metric(interface, metric: SFMRAssertMetric) -> None:
        print('recv_worse_metric, L -> W')

        interface.set_assert_state(AssertState.Winner)
        interface.set_winner_metric(None)
        interface.send_assert()

    @staticmethod
    def aw_failure(interface: SFMRAssertImplABC) -> None:
        print('aw_failure, L -> W')

        interface.set_assert_state(AssertState.Winner)
        interface.set_winner_metric(None)
        interface.send_assert()

    @staticmethod
    def al_rpc_better_than_aw(interface: SFMRAssertImplABC) -> None:
        print('al_rpc_improves, L -> W')

        interface.set_assert_state(AssertState.Winner)
        interface.set_winner_metric(None)
        interface.send_assert()

    @staticmethod
    def aw_rpc_worsens(interface: SFMRAssertImplABC) -> None:
        assert False  # pragma: no cover



class AssertState():
    Winner = SFMRAssertWinner()
    Looser = SFMRAssertLooser()
