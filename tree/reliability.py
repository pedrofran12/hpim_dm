from abc import ABCMeta, abstractmethod
#from typing import Union


#SFMRPruneStateType = Union['SFMRNoInfo', 'SFMRDownstreamInterested',
#                           'SFMRDownstreamInterestedPending',
#                           'SFMRNoDownstreamInterested', ]

from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .tree_interface import TreeInterface

class MessageReliabilityABC():
    @staticmethod
    def send_new_interest(interface: 'TreeInterface') -> None:
        interface.set_message_state(MessageReliabilityStates.INTEREST)
        aw = interface._best_upstream_router.get_ip()
        pkt = interface.create_interest_msg()
        interface._msg_being_reliably_sent = (pkt, aw)
        interface.resend_last_reliable_packet()
        interface.set_retransmission_timer()

    @staticmethod
    def send_new_no_interest(interface: 'TreeInterface') -> None:
        interface.set_message_state(MessageReliabilityStates.INTEREST)
        aw = interface._best_upstream_router.get_ip()
        pkt = interface.create_no_interest_msg()
        interface._msg_being_reliably_sent = (pkt, aw)
        interface.resend_last_reliable_packet()
        interface.set_retransmission_timer()

    @staticmethod
    def send_new_i_am_upstream(interface: 'TreeInterface', rpc) -> None:
        interface.set_message_state(MessageReliabilityStates.UPSTREAM)
        pkt = interface.create_install_msg(rpc.metric_preference, rpc.route_metric)
        interface._msg_being_reliably_sent = (pkt, None)
        interface.set_retransmission_timer()
        interface.clear_neighbors_that_acked_list()
        interface.resend_last_reliable_packet()

    @staticmethod
    def send_new_i_am_no_longer_upstream(interface: 'TreeInterface') -> None:
        interface.set_message_state(MessageReliabilityStates.UPSTREAM)
        pkt = interface.create_uninstall_msg()
        interface._msg_being_reliably_sent = (pkt, None)
        interface.set_retransmission_timer()
        interface.clear_neighbors_that_acked_list()
        interface.resend_last_reliable_packet()

    @staticmethod
    def retransmission_timer_expires(interface: 'TreeInterface') -> None:
        return

    @staticmethod
    def receive_ack_and_sn_is_fresh(interface: 'TreeInterface', neighbor_ip) -> None:
        return

    @staticmethod
    def all_neighbors_acked(interface: 'TreeInterface') -> None:
        interface.clear_retransmission_timer()
        interface.message_has_been_reliable_transmitted()

    @staticmethod
    def cancel_message(interface: 'TreeInterface') -> None:
        interface.clear_retransmission_timer()


class InterestMessageReliability(MessageReliabilityABC):
    @staticmethod
    def receive_ack_and_sn_is_fresh(interface: 'TreeInterface', neighbor_ip):
        MessageReliabilityABC.all_neighbors_acked(interface)

    @staticmethod
    def retransmission_timer_expires(interface: 'TreeInterface'):
        interface.set_retransmission_timer()
        interface.resend_last_reliable_packet()


class UpstreamMessageReliability(MessageReliabilityABC):
    @staticmethod
    def receive_ack_and_sn_is_fresh(interface: 'TreeInterface', neighbor_ip) -> None:
        interface.neighbor_acked(neighbor_ip)

    @staticmethod
    def retransmission_timer_expires(interface: 'TreeInterface'):
        if interface.did_all_neighbors_acked():
            UpstreamMessageReliability.all_neighbors_acked(interface)
            return

        interface.resend_last_reliable_packet()
        interface.set_retransmission_timer()


class MessageReliabilityStates():
    UPSTREAM = UpstreamMessageReliability()
    INTEREST = InterestMessageReliability()
