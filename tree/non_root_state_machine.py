from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_downstream import TreeInterfaceDownstream


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
