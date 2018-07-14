from .tree_interface import TreeInterface
from .root_state_machine import SFMRRootState

import traceback
from . import DataPacketsSocket
import threading
import logging
import Main


class TreeInterfaceUpstream(TreeInterface):
    LOGGER = logging.getLogger('protocol.KernelEntry.RootInterface')

    def __init__(self, kernel_entry, interface_id, best_upstream_router, was_non_root=False, previous_tree_state=None, current_tree_state=None):
        extra_dict_logger = kernel_entry.kernel_entry_logger.extra.copy()
        extra_dict_logger['vif'] = interface_id
        extra_dict_logger['interfacename'] = Main.kernel.vif_index_to_name_dic[interface_id]
        logger = logging.LoggerAdapter(TreeInterfaceUpstream.LOGGER, extra_dict_logger)
        TreeInterface.__init__(self, kernel_entry, interface_id, best_upstream_router, logger)

        from .root_state_machine import SFMRRootState
        self.current_tree_state = current_tree_state
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
        (s,g) = self.get_tree_id()
        interface_name = self.get_interface().interface_name
        self.socket_pkt = DataPacketsSocket.get_s_g_bpf_filter_code(s, g, interface_name)

        # run receive method in background
        receive_thread = threading.Thread(target=self.socket_recv)
        receive_thread.daemon = True
        receive_thread.start()

        self.logger.debug('Created UpstreamInterface')


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
            #self._upstream_state.recv_uninstall_from_aw_and_there_are_no_upstream_routers(self)
            #self.transition_to_inactive()
            #self._upstream_state.tree_transitions_to_inactive_or_unknown_state(self)
            # TODO CANCELAR MSG ANTERIOR???
            return

        elif best_upstream_router is None or best_upstream_router is not assert_state:
            print("ASSERT IS ELIF")
            #self._upstream_state.tree_is_active_and_best_upstream_router_reelected(self)
            # EVENT 6 and 7
            #self._upstream_state.tree_is_active_and_best_upstream_router_reelected(self)
            SFMRRootState.tree_is_active_and_best_upstream_router_reelected(self)
        else:
            print("ELSE")
        '''
        elif best_upstream_router is None or best_upstream_router is not assert_state:
            print("ASSERT IS ELIF")
            self._upstream_state.recv_install_from_aw(self)
            #self.transition_to_active()
        '''


    def change_interest_state(self, interest_state):
        return


    ############################################
    #
    ############################################
    def tree_transition_to_active(self):
        from .KernelEntry import ActiveTree
        self.current_tree_state = ActiveTree
        SFMRRootState.tree_transitions_to_active_state(self)

    def tree_transition_to_inactive(self):
        from .KernelEntry import InactiveTree
        self.current_tree_state = InactiveTree

    def tree_transition_to_unknown(self):
        from .KernelEntry import UnknownTree
        self.current_tree_state = UnknownTree

    ###########################################
    # Change to in/out-tree
    ###########################################
    def send_my_interest(self):
        if self.is_node_in_tree() and not self.is_S_directly_conn():
            #self._message_state.send_new_interest(self)
            self.send_interest()
        elif not self.is_S_directly_conn():
            #self._message_state.send_new_no_interest(self)
            self.send_no_interest()

    # event 5
    def node_is_out_tree(self, force=False):
        #if not self.is_S_directly_conn() and (self._was_in_tree or force) and self._best_upstream_router is not None:
        if self.is_tree_active() and not self.is_S_directly_conn() and self._best_upstream_router is not None:
            #self._upstream_state.transition_to_it_or_ot_and_active_tree(self)
            SFMRRootState.transition_to_it_or_ot_and_active_tree(self)

    # event 5
    def node_is_in_tree(self, force=False):
        #if not self.is_S_directly_conn() and (not self._was_in_tree or force) and self._best_upstream_router is not None:
        if self.is_tree_active() and not self.is_S_directly_conn() and self._best_upstream_router is not None:
            #self._upstream_state.transition_to_it_or_ot_and_active_tree(self)
            SFMRRootState.transition_to_it_or_ot_and_active_tree(self)

    ###########################################
    # Changes to RPF'(s)
    ###########################################
    # caused by unicast routing table:
    '''
    def change_on_unicast_routing(self, interface_change=False):
        self.change_rpf(self.is_node_in_tree(), interface_change)
    
        if self.is_S_directly_conn():
            self._graft_prune_state.sourceIsNowDirectConnect(self)
        else:
            self._originator_state.SourceNotConnected(self)
    '''

    ####################################################################
    #Override
    def is_forwarding(self):
        return False

    #Override
    def delete(self):
        self.socket_is_enabled = False
        self.socket_pkt.close()
        super().delete()
        #self.cancel_message()

    def is_downstream(self):
        return False
