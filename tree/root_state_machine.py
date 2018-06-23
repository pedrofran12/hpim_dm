from abc import ABCMeta, abstractmethod
#from typing import Union


#SFMRPruneStateType = Union['SFMRNoInfo', 'SFMRDownstreamInterested',
#                           'SFMRDownstreamInterestedPending',
#                           'SFMRNoDownstreamInterested', ]
from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_upstream import TreeInterfaceUpstream


'''
class SFMRRootStateABC():
    @staticmethod
    def new_tree_discovered_in_active_state(interface: 'TreeInterfaceUpstream') -> None:
        interface.set_root_interface_state(SFMRRootStates.NOT_UPSTREAM_PENDING)
        interface.send_my_interest()

    @staticmethod
    def non_root_to_root_interface(interface: 'TreeInterfaceUpstream', neighbor_ip) -> None:
        interface.set_root_interface_state(SFMRRootStates.NOT_UPSTREAM)
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def message_has_been_reliably_transmitted(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def transition_to_it_or_ot_and_active_tree(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def tree_is_active_and_best_upstream_router_reelected(interface: 'TreeInterfaceUpstream') -> None:
        return

    @staticmethod
    def tree_transitions_to_inactive_or_unknown_state(interface: 'TreeInterfaceUpstream'):
        return


class SFMRRootNotUpstreamPendingState(SFMRRootStateABC):
    @staticmethod
    def message_has_been_reliably_transmitted(interface: 'TreeInterfaceUpstream') -> None:
        interface.set_root_interface_state(SFMRRootStates.NOT_UPSTREAM)
        interface.send_my_interest()

class SFMRRootNotUpstreamState(SFMRRootStateABC):
    @staticmethod
    def transition_to_it_or_ot_and_active_tree(interface: 'TreeInterfaceUpstream'):
        interface.send_my_interest()

    @staticmethod
    def tree_is_active_and_best_upstream_router_reelected(interface: 'TreeInterfaceUpstream') -> None:
        interface.send_my_interest()

    @staticmethod
    def tree_transitions_to_inactive_or_unknown_state(interface: 'TreeInterfaceUpstream'):
        interface.cancel_message()


class SFMRRootStates:
    NOT_UPSTREAM_PENDING = SFMRRootNotUpstreamPendingState()
    NOT_UPSTREAM = SFMRRootNotUpstreamState()
'''

class SFMRRootState():
    @staticmethod
    def tree_transitions_to_active_state(interface: 'TreeInterfaceUpstream') -> None:
        interface.send_my_interest()

    @staticmethod
    def non_root_to_root_interface(interface: 'TreeInterfaceUpstream', non_root_was_upstream=False) -> None:
        if non_root_was_upstream:
            interface.send_i_am_no_longer_upstream()
        if interface.is_tree_active():
            interface.send_my_interest()

    @staticmethod
    def transition_to_it_or_ot_and_active_tree(interface: 'TreeInterfaceUpstream') -> None:
        interface.send_my_interest()

    @staticmethod
    def tree_is_active_and_best_upstream_router_reelected(interface: 'TreeInterfaceUpstream') -> None:
        interface.send_my_interest()

    @staticmethod
    def tree_transitions_to_inactive_or_unknown_state(interface: 'TreeInterfaceUpstream'):
        interface.cancel_message()
