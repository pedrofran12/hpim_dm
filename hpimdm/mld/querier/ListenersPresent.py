from hpimdm.packet.PacketMLDHeader import PacketMLDHeader
from hpimdm.utils import TYPE_CHECKING
from ..mld_globals import LastListenerQueryInterval
from ..wrapper import CheckingListeners, NoListenersPresent
if TYPE_CHECKING:
    from ..GroupState import GroupState


def receive_report(group_state: 'GroupState'):
    group_state.group_state_logger.debug('Querier ListenersPresent: receive_report')
    group_state.set_timer()


def receive_done(group_state: 'GroupState'):
    group_state.group_state_logger.debug('Querier ListenersPresent: receive_done')
    group_ip = group_state.group_ip

    group_state.set_timer(alternative=True)
    group_state.set_retransmit_timer()

    packet = PacketMLDHeader(type=PacketMLDHeader.MULTICAST_LISTENER_QUERY_TYPE, max_resp_delay=LastListenerQueryInterval, group_address=group_ip)
    group_state.router_state.send(data=packet.bytes(), address=group_ip)

    group_state.set_state(CheckingListeners)


def receive_group_specific_query(group_state: 'GroupState', max_response_time):
    group_state.group_state_logger.debug('Querier ListenersPresent: receive_group_specific_query')
    # do nothing
    return


def group_membership_timeout(group_state: 'GroupState'):
    group_state.group_state_logger.debug('Querier ListenersPresent: group_membership_timeout')
    group_state.set_state(NoListenersPresent)

    # NOTIFY ROUTING - !!!!
    group_state.notify_routing_remove()


def retransmit_timeout(group_state: 'GroupState'):
    group_state.group_state_logger.debug('Querier ListenersPresent: retransmit_timeout')
    # do nothing
    return

