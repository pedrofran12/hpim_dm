from abc import ABCMeta, abstractmethod
#from typing import Union


#SFMRPruneStateType = Union['SFMRNoInfo', 'SFMRDownstreamInterested',
#                           'SFMRDownstreamInterestedPending',
#                           'SFMRNoDownstreamInterested', ]
from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_upstream import TreeInterfaceUpstream

'''
class 'TreeInterfaceUpstream'(metaclass=ABCMeta):
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
'''

class SFMRRootStateABC():
    @staticmethod
    def non_root_interface_to_root_interface(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def neighbor_acks_and_sn_is_fresh(interface: 'TreeInterfaceUpstream', neighbor_ip) -> None:
        return

    @staticmethod
    def all_neighbors_acked_and_there_is_aw(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def all_neighbors_acked_and_there_is_no_aw(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def block_timer_expires(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def interest_timer_expires(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def transition_to_it(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def transition_to_ot(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def recv_install_from_aw(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def recv_uninstall_from_aw_and_there_are_upstream_routers(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def recv_uninstall_from_aw_and_there_are_no_upstream_routers(interface: 'TreeInterfaceUpstream'):
        return


class SFMRUpstreamInterfaceBlocked(SFMRRootStateABC):
    @staticmethod
    def non_root_interface_to_root_interface(interface: 'TreeInterfaceUpstream') -> None:
        pkt = interface.create_uninstall_msg()
        interface._msg_being_reliably_sent = (pkt, "224.0.0.13")
        interface.set_block_timer()
        interface.clear_neighbors_that_acked_list()
        interface.resend_last_reliable_packet()

    @staticmethod
    def neighbor_acks_and_sn_is_fresh(interface: 'TreeInterfaceUpstream', neighbor_ip) -> None:
        interface.check_if_all_neighbors_acked(neighbor_ip)

    @staticmethod
    def all_neighbors_acked_and_there_is_aw(interface: 'TreeInterfaceUpstream') -> None:
        interface.set_upstream_state(SFMRUpstreamStates.UNBLOCKED)
        interface.clear_block_timer()
        interface.send_my_interest()
        interface.set_interest_timer()

    @staticmethod
    def all_neighbors_acked_and_there_is_no_aw(interface: 'TreeInterfaceUpstream') -> None:
        interface.set_upstream_state(SFMRUpstreamStates.UNBLOCKED)
        interface.clear_block_timer()

    @staticmethod
    def block_timer_expires(interface: 'TreeInterfaceUpstream') -> None:
        interface.resend_last_reliable_packet()
        interface.set_block_timer()

class SFMRUpstreamInterfaceUnBlocked(SFMRRootStateABC):
    @staticmethod
    def neighbor_acks_and_sn_is_fresh(interface: 'TreeInterfaceUpstream', neighbor_ip) -> None:
        interface.clear_interest_timer()

    @staticmethod
    def interest_timer_expires(interface: 'TreeInterfaceUpstream') -> None:
        interface.resend_last_reliable_packet()
        interface.set_interest_timer()

    @staticmethod
    def transition_to_it(interface: 'TreeInterfaceUpstream') -> None:
        aw = interface._best_upstream_router.get_ip()
        pkt = interface.create_interest_msg()
        interface._msg_being_reliably_sent = (pkt, aw)
        interface.resend_last_reliable_packet()
        interface.set_interest_timer()

    @staticmethod
    def transition_to_ot(interface: 'TreeInterfaceUpstream') -> None:
        aw = interface._best_upstream_router.get_ip()
        pkt = interface.create_no_interest_msg()
        interface._msg_being_reliably_sent = (pkt, aw)
        interface.resend_last_reliable_packet()
        interface.set_interest_timer()

    @staticmethod
    def recv_install_from_aw(interface: 'TreeInterfaceUpstream') -> None:
        interface.send_my_interest()

    @staticmethod
    def recv_uninstall_from_aw_and_there_are_upstream_routers(interface: 'TreeInterfaceUpstream') -> None:
        interface.send_my_interest()

    @staticmethod
    def recv_uninstall_from_aw_and_there_are_no_upstream_routers(interface: 'TreeInterfaceUpstream'):
        interface.clear_interest_timer()
        return
        # todo informar kernel entry

class SFMRUpstreamStates:
    BLOCKED = SFMRUpstreamInterfaceBlocked()
    UNBLOCKED = SFMRUpstreamInterfaceUnBlocked()
