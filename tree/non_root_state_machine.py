from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_downstream import TreeInterfaceDownstream

'''
class SFMRNonRootStateABC():
    @staticmethod
    def root_interface_to_non_root_or_new_tree_or_transition_to_active(interface: 'TreeInterfaceDownstream') -> None:
        if interface.number_of_neighbors() > 0:
            interface.send_i_am_upstream()

        interface.set_non_root_interface_state(SFMRNonRootState.UPSTREAM)

    @staticmethod
    def tree_transitions_to_inactive_or_unknown(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def message_has_been_reliably_transmitted(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        return


class SFMRNonRootUpstreamState(SFMRNonRootStateABC):
    @staticmethod
    def tree_transitions_to_inactive_or_unknown(interface: 'TreeInterfaceDownstream') -> None:
        if interface.number_of_neighbors() > 0:
            interface.send_i_am_no_longer_upstream()
            interface.set_non_root_interface_state(SFMRNonRootState.NOT_UPSTREAM_PENDING)
        else:
            SFMRNonRootState.NOT_UPSTREAM_PENDING.message_has_been_reliably_transmitted(interface)

    @staticmethod
    def message_has_been_reliably_transmitted(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        if interface.number_of_neighbors() > 0:
            interface.send_i_am_upstream()


class SFMRNonRootNotUpstreamPendingState(SFMRNonRootStateABC):
    @staticmethod
    def tree_transitions_to_inactive_or_unknown(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def message_has_been_reliably_transmitted(interface: 'TreeInterfaceDownstream') -> None:
        interface.set_non_root_interface_state(SFMRNonRootState.NOT_UPSTREAM)
        if interface._best_upstream_router is not None:
            interface.send_no_interest()

    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        return


class SFMRNonRootNotUpstreamState(SFMRNonRootStateABC):
    @staticmethod
    def tree_transitions_to_inactive_or_unknown(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def message_has_been_reliably_transmitted(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        if interface._best_upstream_router is not None:
            interface.send_no_interest()
        else:
            interface.cancel_message()

    @staticmethod
    def my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        return


class SFMRNonRootState():
    UPSTREAM = SFMRNonRootUpstreamState()
    NOT_UPSTREAM_PENDING = SFMRNonRootNotUpstreamPendingState()
    NOT_UPSTREAM = SFMRNonRootNotUpstreamState()
'''

'''
class SFMRNonRootStateABC():
    @staticmethod
    def root_interface_to_non_root_or_new_tree_or_transition_to_active(interface: 'TreeInterfaceDownstream') -> None:
        interface.send_i_am_upstream()
        interface.set_non_root_interface_state(SFMRNonRootState.UPSTREAM)

    @staticmethod
    def tree_transitions_to_inactive_or_unknown(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        return


class SFMRNonRootUpstreamState(SFMRNonRootStateABC):
    @staticmethod
    def tree_transitions_to_inactive_or_unknown(interface: 'TreeInterfaceDownstream') -> None:
        interface.set_non_root_interface_state(SFMRNonRootState.NOT_UPSTREAM)
        interface.send_i_am_no_longer_upstream()
        if interface._best_upstream_router is not None:
            interface.send_no_interest()

    @staticmethod
    def my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        interface.send_i_am_upstream()


class SFMRNonRootNotUpstreamState(SFMRNonRootStateABC):
    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        if interface._best_upstream_router is None:
            interface.cancel_message()
        else:
            interface.send_no_interest()
'''
# NEW STATE MACHINE

class SFMRNonRootStateABCNEW():
    @staticmethod
    def interfaces_roles_dont_change_and_tree_transitions_to_active_state(interface: 'TreeInterfaceDownstream') -> None:
        interface.send_i_am_upstream()

    @staticmethod
    def interfaces_roles_change_and_tree_remains_or_transitions_to_active_state(interface: 'TreeInterfaceDownstream') -> None:
        interface.send_i_am_upstream()

    @staticmethod
    def tree_transitions_from_active_to_inactive_and_best_upstream_neighbor_is_null(interface: 'TreeInterfaceDownstream'):
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def tree_transitions_from_active_to_unknown(interface: 'TreeInterfaceDownstream'):
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def tree_transitions_from_active_to_inactive_and_best_upstream_neighbor_is_not_null(interface: 'TreeInterfaceDownstream'):
        interface.send_i_am_no_longer_upstream()
        interface.send_no_interest()

    '''
    @staticmethod
    def tree_remains_in_inactive_state_and_best_upstream_neighbors_didnt_change_after_receiving_i_am_upstream(interface: 'TreeInterfaceDownstream'):
        interface.send_no_interest()

    @staticmethod
    def tree_remains_in_inactive_state_and_best_upstream_neighbors_changes_and_not_null(interface: 'TreeInterfaceDownstream'):
        interface.send_no_interest()
    '''

    @staticmethod
    def tree_remains_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream'):
        interface.send_no_interest()

    @staticmethod
    def tree_transitions_from_unknown_to_inactive_and_best_upstream_is_not_null(interface: 'TreeInterfaceDownstream'):
        interface.send_no_interest()


    '''
    @staticmethod
    def tree_is_inactive_and_best_upstream_router_reelected(interface: 'TreeInterfaceDownstream') -> None:
        return
    '''

    @staticmethod
    def tree_is_active_and_my_rpc_changes(interface: 'TreeInterfaceDownstream') -> None:
        interface.send_i_am_upstream()



'''
class SFMRNonRootState():
    UPSTREAM = SFMRNonRootUpstreamState()
    NOT_UPSTREAM = SFMRNonRootNotUpstreamState()
'''