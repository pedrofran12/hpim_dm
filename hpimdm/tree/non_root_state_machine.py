from hpimdm.utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_non_root import TreeInterfaceNonRoot


class SFMRNonRootState:
    @staticmethod
    def interfaces_roles_dont_change_and_tree_transitions_to_active_state(interface: 'TreeInterfaceNonRoot'):
        """
        Tree transitions to Active state AND
        interface not directly connected to the source AND
        interface roles dont change
        """
        interface.logger.debug('interfaces_roles_dont_change_and_tree_transitions_to_active_state')
        interface.send_i_am_upstream()

    @staticmethod
    def interfaces_roles_change_and_tree_remains_or_transitions_to_active_state(interface: 'TreeInterfaceNonRoot'):
        """
        Tree remains or changes to Active state AND
        interface not directly connected to the source AND
        interface roles change (Root->Non-Root)
        """
        interface.logger.debug('interfaces_roles_change_and_tree_remains_or_transitions_to_active_state')
        interface.send_i_am_upstream()

    @staticmethod
    def tree_transitions_from_active_to_unsure_and_best_upstream_neighbor_is_null(interface: 'TreeInterfaceNonRoot'):
        """
        Tree transitions from Active to Unsure state AND
        BestUpstream neighbor is null
        """
        interface.logger.debug('tree_transitions_from_active_to_unsure_and_best_upstream_neighbor_is_null')
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def tree_transitions_from_active_to_inactive(interface: 'TreeInterfaceNonRoot'):
        """
        Tree transitions from Active to Inactive state
        """
        interface.logger.debug('tree_transitions_from_active_to_inactive')
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def interface_roles_dont_change_and_tree_transitions_from_active_to_unsure_and_best_upstream_neighbor_is_not_null(interface: 'TreeInterfaceNonRoot'):
        """
        Tree transitions from Active to Unsure state AND
        BestUpstream neighbor is not null
        """
        interface.logger.debug('interface_roles_dont_change_and_tree_transitions_from_active_to_unsure_and_best_upstream_neighbor_is_not_null')
        interface.send_i_am_no_longer_upstream()
        interface.send_no_interest()

    @staticmethod
    def interface_roles_change_and_tree_transitions_from_active_to_unsure_and_best_upstream_neighbor_is_not_null(interface: 'TreeInterfaceNonRoot'):
        """
        Tree transitions from Active to Unsure state AND
        BestUpstream neighbor is not null
        """
        interface.logger.debug('interface_roles_change_and_tree_transitions_from_active_to_unsure_and_best_upstream_neighbor_is_not_null')
        interface.send_no_interest()

    @staticmethod
    def tree_remains_unsure_and_best_upstream_router_reelected(interface: 'TreeInterfaceNonRoot'):
        """
        Tree remains in Unsure state AND
        BestUpstream neighbor changes

        OR

        Tree remains in Unsure state AND
        BestUpstream neighbor transmitted IamUpstream message that doesnt cause a change of the BestUpstream neighbor
        """
        interface.logger.debug('tree_remains_unsure_and_best_upstream_router_reelected')
        interface.send_no_interest()

    @staticmethod
    def tree_transitions_from_inactive_to_unsure_and_best_upstream_is_not_null(interface: 'TreeInterfaceNonRoot'):
        """
        Tree transitions from Inactive to Unsure state AND
        BestUpstream neighbor is not null
        """
        interface.logger.debug('tree_transitions_from_inactive_to_unsure_and_best_upstream_is_not_null')
        interface.send_no_interest()

    @staticmethod
    def tree_remains_active_and_my_rpc_changes(interface: 'TreeInterfaceNonRoot'):
        """
        Tree is Active AND
        interface not directly connected to the source AND
        MyRPC changes
        """
        interface.logger.debug('tree_remains_active_and_my_rpc_changes')
        interface.send_i_am_upstream()
