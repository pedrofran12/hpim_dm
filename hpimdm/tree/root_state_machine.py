from hpimdm.utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_root import TreeInterfaceRoot

'''
class SFMRRootState:
    @staticmethod
    def tree_transitions_to_active_state(interface: 'TreeInterfaceRoot') -> None:
        """
        Tree transitions to Active state AND
        interface roles dont change
        """
        interface.logger.debug('tree_transitions_to_active_state')
        interface.send_my_interest()

    @staticmethod
    def tree_remains_in_active_state_and_non_root_transitions_to_root_interface(interface: 'TreeInterfaceRoot'):
        """
        Tree remains in Active state AND
        Non-root interface transitions to Root type
        """
        interface.logger.debug('tree_remains_in_active_state_and_non_root_transitions_to_root_interface')
        interface.send_i_am_no_longer_upstream()
        interface.send_my_interest()

    @staticmethod
    def tree_transitions_from_active_to_inactive_state_due_to_transition_from_non_root_to_root_interface(interface: 'TreeInterfaceRoot'):
        """
        Tree transitions from Active to Inactive state AND
        Non-Root interface transitions to Root type
        """
        interface.logger.debug('tree_transitions_from_active_to_inactive_state_due_to_transition_from_non_root_to_root_interface')
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def tree_transitions_to_active_state_and_non_root_interface_transitions_to_root(interface: 'TreeInterfaceRoot') -> None:
        """
        Tree transitions to Active state AND
        Non-Root interface transitions to Root type
        """
        interface.logger.debug('tree_transitions_to_active_state_and_non_root_interface_transitions_to_root')
        SFMRRootState.tree_transitions_to_active_state(interface)

    @staticmethod
    def transition_to_it_or_ot_and_active_tree(interface: 'TreeInterfaceRoot') -> None:
        """
        Tree is in Active state AND
        interface becomes interested or not interested in receiving data packets
        """
        interface.logger.debug('transition_to_it_or_ot_and_active_tree')
        interface.send_my_interest()

    @staticmethod
    def tree_is_active_and_best_upstream_router_reelected(interface: 'TreeInterfaceRoot') -> None:
        """
        Tree is in Active state AND
        BestUpstream neighbor changes or BestUpstream neighbor sends an IamUpstream message and remains responsible for
        forwarding data packets
        """
        interface.logger.debug('tree_is_active_and_best_upstream_router_reelected')
        interface.send_my_interest()
'''

class SFMRNewRootState:
    @staticmethod
    def interfaces_roles_change_and_tree_remains_active(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles change (NonRoot->Root) AND
        Tree was Active and remains Active
        """
        interface.logger.debug('interfaces_roles_change_and_tree_remains_active')
        interface.send_i_am_no_longer_upstream()
        interface.send_my_interest()

    @staticmethod
    def interfaces_roles_change_and_tree_was_unsure_and_transitions_to_active(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles change (NonRoot->Root) AND
        Tree was Unsure and transitions to Active state
        """
        interface.logger.debug('interfaces_roles_change_and_tree_was_unsure_and_transitions_to_active')
        interface.send_my_interest()

    @staticmethod
    def interfaces_roles_change_and_tree_was_active_and_transitions_to_unsure_and_best_upstream_neighbor_is_null(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles change (NonRoot->Root) AND
        Tree transitions from Active to Unsure state AND
        BestUpstreamNeighbor is null
        """
        interface.logger.debug('interfaces_roles_change_and_tree_was_active_and_transitions_to_unsure_and_best_upstream_neighbor_is_null')
        interface.send_i_am_no_longer_upstream()

    @staticmethod
    def interfaces_roles_change_and_tree_was_active_and_transitions_to_unsure_and_best_upstream_neighbor_not_null(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles change (NonRoot->Root) AND
        Tree transitions from Active to Unsure state AND
        BestUpstreamNeighbor is not null (possible loop detected)
        """
        interface.logger.debug('interfaces_roles_change_and_tree_was_active_and_transitions_to_unsure_and_best_upstream_neighbor_not_null')
        interface.send_i_am_no_longer_upstream()
        interface.send_my_interest()

    @staticmethod
    def interfaces_roles_change_and_tree_remains_unsure_and_best_upstream_neighbor_not_null(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles change (NonRoot->Root) AND
        Tree was Unsure and remains Unsure AND
        BestUpstreamNeighbor is not null (possible loop detected)
        """
        interface.logger.debug('interfaces_roles_change_and_tree_remains_unsure_and_best_upstream_neighbor_not_null')
        interface.send_my_interest()

    @staticmethod
    def interfaces_roles_dont_change_and_router_transition_to_it_or_ot(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles dont change (this interface remains Root) AND
        BestUpstreamNeighbor does not change AND
        router changes its interest in receiving data packets (becomes interested or not interested)
        """
        interface.logger.debug('interfaces_roles_dont_change_and_router_transition_to_it_or_ot')
        interface.send_my_interest()


    @staticmethod
    def interfaces_roles_dont_change_and_best_upstream_neighbor_reelected(interface: 'TreeInterfaceRoot'):
        """
        Interfaces roles dont change (this interface remains Root) AND
        BestUpstreamNeighbor changes AND
        BestUpstreamNeighbor is not null
        (other router was elected as the responsible for forwarding multicast data packets)

        OR

        Interfaces roles dont change (this interface remains Root) AND
        BestUpstreamNeighbor transmitted a new IamUpstream message AND
        that neighbor is still responsible for forwarding multicast data packet
        (a new IamUpstream message was received from the BestUpstreamNeighbor but that router is still responsible for
        forwarding multicast data packets)
        """
        interface.logger.debug('interfaces_roles_dont_change_and_best_upstream_neighbor_reelected')
        interface.send_my_interest()
