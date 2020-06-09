import logging
import traceback
from threading import Thread

from . import data_packets_socket
from .tree_interface import TreeInterface
from .root_state_machine import SFMRNewRootState #SFMRRootState


class TreeInterfaceRoot(TreeInterface):
    LOGGER = logging.getLogger('hpim.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, best_upstream_router, was_non_root, previous_tree_state, current_tree_state):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = kernel_entry.get_interface_name(interface_id)
        logger = logging.LoggerAdapter(TreeInterfaceRoot.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, current_tree_state, logger)

        # event 1
        if was_non_root and previous_tree_state.is_active() and current_tree_state.is_active():
            SFMRNewRootState.interfaces_roles_change_and_tree_remains_active(self)
        # event 2
        elif was_non_root and previous_tree_state.is_unsure() and current_tree_state.is_active():
            SFMRNewRootState.interfaces_roles_change_and_tree_was_unsure_and_transitions_to_active(self)
        # event 3
        elif was_non_root and previous_tree_state.is_active() and current_tree_state.is_unsure() and \
                best_upstream_router is None:
            SFMRNewRootState.interfaces_roles_change_and_tree_was_active_and_transitions_to_unsure_and_best_upstream_neighbor_is_null(self)
        # event 4
        elif was_non_root and previous_tree_state.is_active() and current_tree_state.is_unsure() and \
                best_upstream_router is not None:
            SFMRNewRootState.interfaces_roles_change_and_tree_was_active_and_transitions_to_unsure_and_best_upstream_neighbor_not_null(self)
        # event 5
        elif was_non_root and previous_tree_state.is_unsure() and current_tree_state.is_unsure() and \
                best_upstream_router is not None:
            SFMRNewRootState.interfaces_roles_change_and_tree_remains_unsure_and_best_upstream_neighbor_not_null(self)
        # event 6
        elif not was_non_root and best_upstream_router is not None:
            SFMRNewRootState.interfaces_roles_dont_change_and_best_upstream_neighbor_reelected(self)

        # Originator state
        # TODO TESTE SOCKET RECV DATA PCKTS
        self.socket_is_enabled = True
        (s, g) = self.get_tree_id()
        interface_name = self.get_interface_name()
        self.socket_pkt = data_packets_socket.get_s_g_bpf_filter_code(s, g, interface_name)

        # run receive method in background
        receive_thread = Thread(target=self.socket_recv)
        receive_thread.daemon = True
        receive_thread.start()

        self.logger.debug('Created RootInterface')


    def socket_recv(self):
        while self.socket_is_enabled:
            try:
                self.socket_pkt.recvfrom(0)
                print("DATA RECEIVED")
                self.recv_data_msg()
            except:
                traceback.print_exc()
                continue

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        """
        This root interface received a data packet
        """
        return

    def change_best_upstream_neighbor_state(self, best_upstream_neighbor_state):
        """
        A neighbor changed Upstream state due to the reception of any control packet
        (IamUpstream or IamNoLongerUpstream or Interest or NoInterest or Sync)
        """
        previous_best_upstream_router = self._best_upstream_router
        super().change_best_upstream_neighbor_state(best_upstream_neighbor_state)
        print(self.get_tree_id())
        print("UPSTREAM CHANGE ASSERT STATE")
        print("best:", previous_best_upstream_router)
        print("new best", best_upstream_neighbor_state)

        if best_upstream_neighbor_state is None:
            print("ASSERT IS NONE")
            return
        elif previous_best_upstream_router is None or previous_best_upstream_router is not best_upstream_neighbor_state:
            print("BEST UPSTREAM REELECTED")
            # EVENT 6 and 8
            SFMRNewRootState.interfaces_roles_dont_change_and_best_upstream_neighbor_reelected(self)

    ###########################################
    # Change to in/out-tree
    ###########################################
    def send_my_interest(self):
        """
        Send an Interest/NoInterest message through this interface based on the IT/OT state of this router
        """
        if self.is_node_in_tree():
            self.send_interest()
        else:
            self.send_no_interest()

    def node_is_out_tree(self):
        """
        Node is no longer interested in receiving data packets...
        React to this event in order to transmit some control packets
        """
        if self._best_upstream_router is not None:
            # event 7
            SFMRNewRootState.interfaces_roles_dont_change_and_router_transition_to_it_or_ot(self)

    def node_is_in_tree(self):
        """
        Node is no longer interested in receiving data packets...
        React to this event in order to transmit some control packets
        """
        if self._best_upstream_router is not None:
            # event 7
            SFMRNewRootState.interfaces_roles_dont_change_and_router_transition_to_it_or_ot(self)

    ####################################################################
    def is_forwarding(self):
        """
        This interface must not be included in the OIL of the multicast routing table, thus returning False
        """
        return False

    def delete(self):
        """
        Tree interface is being removed... due to change of interface roles or
        due to the removal of the tree by this router
        Clear all state from this interface regarding this tree
        """
        self.socket_is_enabled = False
        self.socket_pkt.close()
        super().delete()
