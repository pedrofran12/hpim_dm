import logging
import traceback
from threading import Thread

import Main
from . import DataPacketsSocket
from .tree_interface import TreeInterface
from .root_state_machine import SFMRRootState


class TreeInterfaceUpstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, best_upstream_router, was_non_root, previous_tree_state, current_tree_state):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceUpstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, current_tree_state, logger)

        # event 1
        if not previous_tree_state.is_active() and current_tree_state.is_active() and not was_non_root:
            SFMRRootState.tree_transitions_to_active_state(self)
        # event 2
        elif was_non_root and previous_tree_state.is_active() and current_tree_state.is_active():
            SFMRRootState.tree_remains_in_active_state_and_non_root_transitions_to_root_interface(self)
        # event 3
        elif was_non_root and previous_tree_state.is_active() and current_tree_state.is_inactive():
            SFMRRootState.tree_transitions_from_active_to_inactive_state_due_to_transition_from_non_root_to_root_interface(self)
        # event 4
        elif was_non_root and not previous_tree_state.is_active() and current_tree_state.is_active():
            SFMRRootState.tree_transitions_to_active_state_and_non_root_interface_transitions_to_root(self)

        # Originator state
        # TODO TESTE SOCKET RECV DATA PCKTS
        self.socket_is_enabled = True
        (s, g) = self.get_tree_id()
        interface_name = self.get_interface().interface_name
        self.socket_pkt = DataPacketsSocket.get_s_g_bpf_filter_code(s, g, interface_name)

        # run receive method in background
        receive_thread = Thread(target=self.socket_recv)
        receive_thread.daemon = True
        receive_thread.start()

        self.logger.debug('Created RootInterface')


    def socket_recv(self):
        while self.socket_is_enabled:
            try:
                self.socket_pkt.recvfrom(0)
                print("PACOTE DADOS RECEBIDO")
                self.recv_data_msg()
            except:
                traceback.print_exc()
                continue

    ###########################################
    # Recv packets
    ###########################################
    def recv_data_msg(self):
        return

    def change_assert_state(self, assert_state):
        best_upstream_router = self._best_upstream_router
        super().change_assert_state(assert_state)
        print(self.get_tree_id())
        print("UPSTREAM CHANGE ASSERT STATE")
        print("best:", best_upstream_router)
        print("new best", assert_state)

        if assert_state is None:
            print("ASSERT IS NONE")
            return

        elif best_upstream_router is None or best_upstream_router is not assert_state:
            print("ASSERT IS ELIF")
            # EVENT 6 and 7
            SFMRRootState.tree_is_active_and_best_upstream_router_reelected(self)
        else:
            print("ELSE")

    def change_interest_state(self, interest_state):
        return

    ############################################
    # Tree transitions
    ############################################
    def tree_transition_to_active(self):
        if not self.is_tree_active():
            super().tree_transition_to_active()
            SFMRRootState.tree_transitions_to_active_state(self)

    ###########################################
    # Change to in/out-tree
    ###########################################
    def send_my_interest(self):
        if self.is_node_in_tree():
            self.send_interest()
        else:
            self.send_no_interest()

    # event 5
    def node_is_out_tree(self):
        if self.is_tree_active() and self._best_upstream_router is not None:
            SFMRRootState.transition_to_it_or_ot_and_active_tree(self)

    # event 5
    def node_is_in_tree(self):
        if self.is_tree_active() and self._best_upstream_router is not None:
            SFMRRootState.transition_to_it_or_ot_and_active_tree(self)

    ####################################################################
    def is_forwarding(self):
        return False

    def delete(self):
        self.socket_is_enabled = False
        self.socket_pkt.close()
        super().delete()
