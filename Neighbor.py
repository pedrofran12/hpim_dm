import time
import logging
import ipaddress
from threading import Timer

import Main
from utils import TYPE_CHECKING
from tree.metric import AssertMetric
from tree import protocol_globals
from Packet.Packet import Packet
if protocol_globals.MSG_FORMAT == "BINARY":
    from Packet.PacketProtocolAck import PacketNewProtocolAck as PacketProtocolAck
    from Packet.PacketProtocolSync import PacketNewProtocolSync as PacketProtocolHelloSync
    from Packet.PacketProtocolHeader import PacketNewProtocolHeader as PacketProtocolHeader
else:
    from Packet.PacketProtocolAck import PacketProtocolAck
    from Packet.PacketProtocolSync import PacketProtocolHelloSync
    from Packet.PacketProtocolHeader import PacketProtocolHeader

if TYPE_CHECKING:
    from InterfaceProtocol import InterfaceProtocol

DEFAULT_HELLO_HOLD_TIME_DURING_SYNC = 25
DEFAULT_HELLO_HOLD_TIME_AFTER_SYNC = 120

class NeighborState():
    @staticmethod
    def new_neighbor_or_adjacency_reset(neighbor):
        print("NEW NEIG")
        neighbor.set_sync_state(Slave)

        neighbor.start_snapshot()

        # Remove all info from neighbor (if already knew it)
        neighbor.tree_interest_state.clear()
        neighbor.tree_metric_state.clear()
        neighbor.last_sequence_number.clear()
        neighbor.current_sync_sn = 0
        neighbor.neighbor_snapshot_sn = 0
        neighbor.checkpoint_sn = 0
        #

        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[0:5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > 0
        my_snapshot_sn = neighbor.my_snapshot_sequencer

        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, 0,
                                        sync_sn=neighbor.current_sync_sn,
                                        upstream_trees=my_snapshot_mrt, master_flag=True,
                                        more_flag=my_more_bit,
                                        neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
        neighbor.contact_interface.send(pkt, neighbor.ip)
        neighbor.set_sync_timer()
        neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)

    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        return

    @staticmethod
    def sync_timer_expires(neighbor):
        return


class Updated(NeighborState):
    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.neighbor_snapshot_sn > neighbor_snapshot_sn:
            return
        elif neighbor.neighbor_snapshot_sn < neighbor_snapshot_sn:
            Updated.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            return

        if master_bit and neighbor.my_snapshot_sequencer == my_snapshot_sn:
            pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_snapshot_sn, sync_sn=sync_sn,
                                            master_flag=False, more_flag=False,
                                            neighbor_boot_time=neighbor.time_of_boot)
            pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
            neighbor.send(pkt)
            neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)


class Master(NeighborState):
    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.current_sync_sn == 0 and neighbor.neighbor_snapshot_sn == 0:
            neighbor.neighbor_snapshot_sn = neighbor_snapshot_sn

        if neighbor.neighbor_snapshot_sn > neighbor_snapshot_sn:
            return
        elif neighbor.neighbor_snapshot_sn < neighbor_snapshot_sn:
            Master.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            print("EXIT MASTER")
            return

        if master_bit and (sync_sn > 0 and neighbor.my_snapshot_sequencer == my_snapshot_sn or sync_sn == 0):
            print("ENTROU MASTER")
            neighbor.install_tree_state(tree_state)

            my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn*5:
                                                                           (neighbor.current_sync_sn+1)*5]
            my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5
            my_snapshot_sn = neighbor.my_snapshot_sequencer
            neighbor_sn = neighbor.neighbor_snapshot_sn

            pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                            sync_sn=neighbor.current_sync_sn,
                                            upstream_trees=my_snapshot_mrt, master_flag=False,
                                            more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
            pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
            neighbor.send(pkt)

            if sync_sn > 0 and not more_bit and not my_more_bit:
                neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_AFTER_SYNC)
                neighbor.set_sync_state(Updated)
                neighbor.clear_sync_timer()
                del neighbor.my_snapshot_multicast_routing_table[:]
            else:
                neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)
                neighbor.set_sync_timer()
                neighbor.current_sync_sn += 1

    @staticmethod
    def sync_timer_expires(neighbor):
        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[(neighbor.current_sync_sn - 1) * 5:
                                                                       neighbor.current_sync_sn * 5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > (neighbor.current_sync_sn - 1) * 5
        my_snapshot_sn = neighbor.my_snapshot_sequencer
        neighbor_sn = neighbor.neighbor_snapshot_sn

        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                        sync_sn=neighbor.current_sync_sn - 1,
                                        upstream_trees=my_snapshot_mrt, master_flag=False,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
        neighbor.send(pkt)
        neighbor.set_sync_timer()


class Slave(NeighborState):
    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.current_sync_sn == 0 and neighbor.neighbor_snapshot_sn == 0:
            neighbor.neighbor_snapshot_sn = neighbor_snapshot_sn

        if neighbor.neighbor_snapshot_sn > neighbor_snapshot_sn:
            return
        elif neighbor.neighbor_snapshot_sn < neighbor_snapshot_sn:
            Slave.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            return

        if sync_sn == 0 and master_bit:
            print("HERE1")
            my_ip = ipaddress.ip_address(neighbor.contact_interface.get_ip())
            neighbor_ip = ipaddress.ip_address(neighbor.ip)
            if my_ip < neighbor_ip:
                print("HERE2")
                neighbor.set_sync_state(Master)
                neighbor.current_sync_sn = 0
                Master.recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit,
                                 more_bit)
            else:
                Slave.sync_timer_expires(neighbor)
        elif not master_bit and neighbor.my_snapshot_sequencer == my_snapshot_sn:
            print("HERE3")
            my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5

            if sync_sn > 0 and not my_more_bit and not more_bit:
                neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_AFTER_SYNC)
                print("HERE4")
                neighbor.set_sync_state(Updated)
                neighbor.clear_sync_timer()
                del neighbor.my_snapshot_multicast_routing_table[:]
            else:
                neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)
                print("HERE5")
                neighbor.current_sync_sn += 1
                neighbor.install_tree_state(tree_state)

                my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn*5:
                                                                               (neighbor.current_sync_sn+1)*5]
                my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5
                my_snapshot_sn = neighbor.my_snapshot_sequencer
                neighbor_sn = neighbor.neighbor_snapshot_sn

                pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                                sync_sn=neighbor.current_sync_sn,
                                                upstream_trees=my_snapshot_mrt, master_flag=True,
                                                more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
                pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
                neighbor.send(pkt)
                neighbor.set_sync_timer()

    @staticmethod
    def sync_timer_expires(neighbor):
        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn * 5:
                                                                       (neighbor.current_sync_sn + 1) * 5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn * 5
        my_snapshot_sn = neighbor.my_snapshot_sequencer
        neighbor_sn = neighbor.neighbor_snapshot_sn

        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                        sync_sn=neighbor.current_sync_sn,
                                        upstream_trees=my_snapshot_mrt, master_flag=True,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
        neighbor.send(pkt)
        neighbor.set_sync_timer()


class Unknown(NeighborState):
    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if sync_sn == 0 and sync_sn == neighbor.current_sync_sn and master_bit:
            neighbor.set_sync_state(Master)
            neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)

            neighbor.start_snapshot()

            # Remove all info from neighbor (if already knew it)
            neighbor.tree_interest_state.clear()
            neighbor.tree_metric_state.clear()
            neighbor.last_sequence_number.clear()
            neighbor.current_sync_sn = 0
            neighbor.neighbor_snapshot_sn = 0
            neighbor.checkpoint_sn = 0
            #

            Master.recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit)
        else:
            Unknown.new_neighbor_or_adjacency_reset(neighbor)


class Neighbor:
    LOGGER = logging.getLogger('protocol.Interface.Neighbor')

    def __init__(self, contact_interface: "InterfaceProtocol", ip, hello_hold_time: int, neighbor_time_of_boot: int,
                 my_interface_boot_time: int):
        if hello_hold_time == protocol_globals.HELLO_HOLD_TIME_TIMEOUT:
            raise Exception
        logger_info = dict(contact_interface.interface_logger.extra)
        logger_info['neighbor_ip'] = ip
        self.neighbor_logger = logging.LoggerAdapter(self.LOGGER, logger_info)

        self.contact_interface = contact_interface
        self.ip = ip
        self.time_of_boot = neighbor_time_of_boot
        self.neighbor_snapshot_sn = 0

        self.neighbor_liveness_timer = None
        self.hello_hold_time = None
        self.set_hello_hold_time(hello_hold_time)
        self.time_of_last_update = time.time()

        self.current_sync_sn = 0

        # Tree Database storage
        self.tree_interest_state = {}
        self.tree_metric_state = {}

        # Control if received control packets should be processed
        # Used to detect msg retransmissions and out of order reception
        self.last_sequence_number = {}

        self.sync_timer = None
        self.neighbor_state = Unknown
        self.neighbor_logger.debug('Neighbor state transitions to ' + self.neighbor_state.__name__)

        # checkpoint sn
        self.checkpoint_sn = 0

        # Information of my snapshot
        self.my_snapshot_boot_time = my_interface_boot_time
        self.my_snapshot_sequencer = 0
        self.my_snapshot_multicast_routing_table = []

    ######################################################################
    # Checkpoint SN
    ######################################################################
    def get_checkpoint_sn(self):
        if self.neighbor_state == Master or self.neighbor_state == Slave:
            return (self.my_snapshot_boot_time, self.my_snapshot_sequencer - 1)
        else:
            return (None, None)

    ######################################################################
    # Sync Timer
    ######################################################################
    def set_sync_timer(self):
        self.clear_sync_timer()
        self.sync_timer = Timer(10, self.sync_timeout)
        self.sync_timer.start()

    def clear_sync_timer(self):
        if self.sync_timer is not None:
            self.sync_timer.cancel()

    ###########################################
    # Sync Timer timeout
    ###########################################
    def sync_timeout(self):
        self.neighbor_state.sync_timer_expires(self)

    ############################################
    # Sync State
    ############################################
    def set_sync_state(self, state):
        if self.neighbor_state == state:
            return

        self.neighbor_state = state
        self.neighbor_logger.debug('Neighbor state transitions to ' + state.__name__ +
                                   ' with MyBootTime=' + str(self.my_snapshot_boot_time) +
                                   '; MySnapshotSN=' + str(self.my_snapshot_sequencer) +
                                   '; NeighborBootTime=' + str(self.time_of_boot) +
                                   '; NeighborSnapshotSN=' + str(self.neighbor_snapshot_sn))
        if state == Updated:
            Main.kernel.recheck_all_trees(self.contact_interface.vif_index)

    def install_tree_state(self, tree_state: list):
        for t in tree_state:
            tree_id = (t.source, t.group)
            if self.last_sequence_number.get(tree_id, 0) > self.neighbor_snapshot_sn:
                continue

            self.tree_metric_state[tree_id] = AssertMetric(metric_preference=t.metric_preference,
                                                           route_metric=t.metric, ip_address=self.ip)

    def remove_tree_state(self, source, group):
        self.tree_interest_state.pop((source, group), None)

    def get_known_trees(self):
        a = set(self.tree_metric_state.keys())
        b = set(self.tree_interest_state.keys())
        return a.union(b)

    ######################################################################
    # Send Messages
    ######################################################################
    def send(self, packet):
        self.contact_interface.send(packet, self.ip)

    ######################################################################
    # Receive Synchronization Messages
    ######################################################################
    def start_sync_process(self):
        self.neighbor_state.new_neighbor_or_adjacency_reset(self)

    def start_snapshot(self):
        (my_snapshot_bt, my_snapshot_sn, my_snapshot_mrt) = self.contact_interface.snapshot_multicast_routing_table()
        self.my_snapshot_boot_time = my_snapshot_bt
        self.my_snapshot_sequencer = my_snapshot_sn
        self.my_snapshot_multicast_routing_table = list(my_snapshot_mrt.values())
        self.contact_interface.neighbor_start_synchronization(self.ip, my_snapshot_bt, my_snapshot_sn)

    def recv_hello(self, boot_time, holdtime, checkpoint_sn):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.neighbor_snapshot_sn = 0
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            return

        if self.neighbor_state == Updated:
            self.time_of_last_update = time.time()
            self.set_hello_hold_time(holdtime)
            self.set_checkpoint_sn(checkpoint_sn)
        elif holdtime == 0:
            self.set_hello_hold_time(holdtime)

    def set_checkpoint_sn(self, checkpoint_sn):
        #if checkpoint_sn > self.neighbor_snapshot_sn:
        #    self.neighbor_snapshot_sn = checkpoint_sn
        if checkpoint_sn > self.checkpoint_sn:
            self.checkpoint_sn = checkpoint_sn

            to_remove = {k for k, v in self.last_sequence_number.items() if v <= checkpoint_sn}
            for k in to_remove:
                self.last_sequence_number.pop(k)

    def recv_sync(self, upstream_trees, my_sn, neighbor_sn, boot_time, sync_sn, master_flag, more_flag, own_interface_boot_time):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot or own_interface_boot_time > self.my_snapshot_boot_time:
            self.time_of_boot = boot_time
            self.neighbor_snapshot_sn = 0
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            return

        self.neighbor_state.recv_sync(self, upstream_trees, my_sn, neighbor_sn, sync_sn, master_flag, more_flag)

    ################################################################################################
    def get_tree_state(self, tree):
        if self.neighbor_state != Updated:
            # do not interpret stored state if not Updated
            return (False, None)
        else:
            upstream_state = self.tree_metric_state.get(tree, None)
            interest_state = False
            if upstream_state is None:
                interest_state = self.tree_interest_state.get(tree, protocol_globals.INITIAL_FLOOD_ENABLED)
            print("INTEREST NEIGHBOR ", self.ip, ":", interest_state)
            print("UPSTREAM NEIGHBOR ", self.ip, ":", upstream_state)
            return (interest_state, upstream_state)

    # decide if should process control packet
    def recv_reliable_packet(self, sn, tree, boot_time):
        if boot_time < self.time_of_boot:
            return False
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.neighbor_snapshot_sn = 0
            self.start_sync_process()
            return False

        #if self.neighbor_state != Updated:
            # do not interpret message during sync
            #return False
        if self.neighbor_state == Unknown or self.current_sync_sn == 0:
            #do not interpret control message without having the guarantee of
            # correct <NeighborBootTime; NeighborSnapshotSN> pair
            return False

        last_received_sn = self.last_sequence_number.get(tree, 0)

        if sn <= self.neighbor_snapshot_sn or sn <= self.checkpoint_sn:
            # dont deliver to application
            print("RCVD ", sn)
            print("NSSN ", self.neighbor_snapshot_sn)
            return False
        elif sn >= last_received_sn:
            (source, group) = tree
            ack = PacketProtocolAck(source, group, sn, neighbor_boot_time=boot_time,
                                    neighbor_snapshot_sn=self.neighbor_snapshot_sn,
                                    my_snapshot_sn=self.my_snapshot_sequencer)
            ph = PacketProtocolHeader(ack, boot_time=self.contact_interface.time_of_boot)
            packet = Packet(payload=ph)
            self.contact_interface.send(packet, self.ip)

            if sn > last_received_sn:
                # update most recent sn received from this neighbor
                self.last_sequence_number[tree] = sn

                # deliver to application
                return True
        # dont deliver to application
        print("RCVD ", sn)
        print("LAST TREE SN ", last_received_sn)
        return False

    # decide if should process ack packet
    def recv_ack(self, my_boot_time, neighbor_boot_time, my_snapshot_sn, neighbor_snapshot):
        if neighbor_boot_time < self.time_of_boot:
            return False
        elif neighbor_boot_time > self.time_of_boot:
            self.time_of_boot = neighbor_boot_time
            self.neighbor_snapshot_sn = 0
            self.start_sync_process()
            return False

        return self.neighbor_state != Unknown and self.current_sync_sn > 0 and \
               self.my_snapshot_boot_time == my_boot_time and self.time_of_boot == neighbor_boot_time and\
               self.my_snapshot_sequencer == my_snapshot_sn and self.neighbor_snapshot_sn == neighbor_snapshot

    ################################################################################################

    def set_hello_hold_time(self, hello_hold_time: int):
        self.hello_hold_time = hello_hold_time
        if self.neighbor_liveness_timer is not None:
            self.neighbor_liveness_timer.cancel()

        if hello_hold_time == protocol_globals.HELLO_HOLD_TIME_TIMEOUT:
            self.remove()
        else:
            self.neighbor_liveness_timer = Timer(hello_hold_time, self.remove)
            self.neighbor_liveness_timer.start()

    def remove(self):
        with self.contact_interface.neighbors_lock:
            print('HELLO TIMER EXPIRED... remove neighbor')
            self.remove_neighbor_state()

            self.contact_interface.remove_neighbor(self.ip)

    def remove_neighbor_state(self):
        self.neighbor_logger.debug('Removing neighbor ' + self.ip)
        if self.neighbor_liveness_timer is not None:
            self.neighbor_liveness_timer.cancel()

        self.clear_sync_timer()

        self.tree_interest_state.clear()
        self.tree_metric_state.clear()
        self.last_sequence_number.clear()
        del self.my_snapshot_multicast_routing_table[:]
