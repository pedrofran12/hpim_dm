from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_upstream import TreeInterfaceUpstream


class SFMRRootState:
    @staticmethod
    def tree_transitions_to_active_state(interface: 'TreeInterfaceUpstream') -> None:
        interface.logger.debug('tree_transitions_to_active_state')
        interface.send_my_interest()

    @staticmethod
    def tree_remains_in_active_state_and_non_root_transitions_to_root_interface(interface: 'TreeInterfaceUpstream'):
        interface.logger.debug('tree_remains_in_active_state_and_non_root_transitions_to_root_interface')
        interface.send_i_am_no_longer_upstream()
        interface.send_my_interest()

    @staticmethod
    def tree_transitions_from_active_to_inactive_state_due_to_transition_from_non_root_to_root_interface(interface: 'TreeInterfaceUpstream'):
        interface.logger.debug('tree_transitions_from_active_to_inactive_state_due_to_transition_from_non_root_to_root_interface')
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def tree_transitions_to_active_state_and_non_root_interface_transitions_to_root(interface: 'TreeInterfaceUpstream') -> None:
        interface.logger.debug('tree_transitions_to_active_state_and_non_root_interface_transitions_to_root')
        SFMRRootState.tree_transitions_to_active_state(interface)

    @staticmethod
    def transition_to_it_or_ot_and_active_tree(interface: 'TreeInterfaceUpstream') -> None:
        interface.logger.debug('transition_to_it_or_ot_and_active_tree')
        interface.send_my_interest()

    @staticmethod
    def tree_is_active_and_best_upstream_router_reelected(interface: 'TreeInterfaceUpstream') -> None:
        interface.logger.debug('tree_is_active_and_best_upstream_router_reelected')
        interface.send_my_interest()
