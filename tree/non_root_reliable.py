from abc import ABCMeta, abstractmethod
#from typing import Union


#SFMRPruneStateType = Union['SFMRNoInfo', 'SFMRDownstreamInterested',
#                           'SFMRDownstreamInterestedPending',
#                           'SFMRNoDownstreamInterested', ]

from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_if_downstream import TreeInterfaceDownstream

'''
class 'TreeInterfaceDownstream'(metaclass=ABCMeta):
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

class SFMRNonRootStateABC():
    @staticmethod
    def root_interface_to_non_root_or_new_tree_or_transition_to_active(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def tree_transitions_to_inactive(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def receive_ack_from_neighbor_and_sn_fresh(interface: 'TreeInterfaceDownstream', neighbor_ip) -> None:
        return

    @staticmethod
    def all_neighbors_acked(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def install_timer_expires(interface: 'TreeInterfaceDownstream') -> None:
        return

    @staticmethod
    def receive_interest_msg(interface: 'TreeInterfaceDownstream', neighbor_ip, is_interested) -> None:
        return

    @staticmethod
    def receive_install_msg(interface: 'TreeInterfaceDownstream', neighbor_ip, state) -> None:
        return

    @staticmethod
    def receive_uninstall_msg(interface: 'TreeInterfaceDownstream', neighbor_ip) -> None:
        return

    @staticmethod
    def rpc_change(interface: 'TreeInterfaceDownstream') -> None:
        return




class SFMRNonRootActiveState(SFMRNonRootStateABC):
    @staticmethod
    def root_interface_to_non_root_or_new_tree_or_transition_to_active(interface: 'TreeInterfaceDownstream') -> None:
        # todo obter rpc!!!!
        #assert_state = interface._upstream_routers[interface.get_ip()]
        if interface.number_of_neighbors() == 0:
            SFMRNonRootActiveState.all_neighbors_acked(interface)
            return
        assert_state = interface._my_assert_rpc
        pkt = interface.create_install_msg(assert_state.metric_preference, assert_state.route_metric)
        interface._msg_being_reliably_sent = pkt
        interface.set_install_timer()
        interface.clear_neighbors_that_acked_list()
        interface.resend_last_reliable_packet()

    @staticmethod
    def receive_ack_from_neighbor_and_sn_fresh(interface: 'TreeInterfaceDownstream', neighbor_ip) -> None:
        interface.neighbor_acked(neighbor_ip)

    @staticmethod
    def all_neighbors_acked(interface: 'TreeInterfaceDownstream') -> None:
        interface.clear_install_timer()

    @staticmethod
    def install_timer_expires(interface: 'TreeInterfaceDownstream') -> None:
        interface.resend_last_reliable_packet()
        interface.set_install_timer()

    @staticmethod
    def receive_interest_msg(interface: 'TreeInterfaceDownstream', neighbor_ip, is_interested) -> None:
        print("RCV_INTEREST_103_NON_ROOT_RELIABLE")
        interface.set_neighbor_interest(neighbor_ip, is_interested)

    @staticmethod
    def receive_install_msg(interface: 'TreeInterfaceDownstream', neighbor_ip, state) -> None:
        interface.set_upstream_node_state(neighbor_ip, state)

    @staticmethod
    def receive_uninstall_msg(interface: 'TreeInterfaceDownstream', neighbor_ip) -> None:
        interface.clear_upstream_node_state(neighbor_ip)

    @staticmethod
    def rpc_change(interface: 'TreeInterfaceDownstream') -> None:
        #assert_state = interface._upstream_routers[interface.get_ip()]
        if interface.number_of_neighbors() == 0:
            SFMRNonRootActiveState.all_neighbors_acked(interface)
            return
        assert_state = interface._my_assert_rpc
        pkt = interface.create_install_msg(assert_state.metric_preference, assert_state.route_metric)
        interface._msg_being_reliably_sent = pkt
        interface.set_install_timer()
        interface.clear_neighbors_that_acked_list()
        interface.resend_last_reliable_packet()


class SFMRNonRootInactiveState(SFMRNonRootStateABC):
    @staticmethod
    def tree_transitions_to_inactive(interface: 'TreeInterfaceDownstream') -> None:
        if interface.number_of_neighbors() == 0:
            SFMRNonRootInactiveState.all_neighbors_acked(interface)
            return
        pkt = interface.create_uninstall_msg()
        interface._msg_being_reliably_sent = pkt
        interface.set_install_timer()
        interface.clear_neighbors_that_acked_list()
        interface.resend_last_reliable_packet()

    @staticmethod
    def receive_ack_from_neighbor_and_sn_fresh(interface: 'TreeInterfaceDownstream', neighbor_ip) -> None:
        interface.neighbor_acked(neighbor_ip)

    @staticmethod
    def all_neighbors_acked(interface: 'TreeInterfaceDownstream') -> None:
        interface.clear_install_timer()
        interface._kernel_entry.notify_interface_is_ready_to_remove(interface._interface_id)

    @staticmethod
    def install_timer_expires(interface: 'TreeInterfaceDownstream') -> None:
        interface.resend_last_reliable_packet()
        interface.set_install_timer()


class SFMRNonRootState():
    ACTIVE = SFMRNonRootActiveState()
    INACTIVE = SFMRNonRootInactiveState()
