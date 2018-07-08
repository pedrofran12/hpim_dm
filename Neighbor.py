from threading import Timer
import time
from utils import HELLO_HOLD_TIME_NO_TIMEOUT, HELLO_HOLD_TIME_TIMEOUT, TYPE_CHECKING
from Packet.PacketProtocolAck import PacketProtocolAck
from Packet.PacketProtocolSync import PacketProtocolHelloSync
from Packet.PacketProtocolHeader import PacketProtocolHeader
from Packet.Packet import Packet
from tree import globals

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
        neighbor.tree_state.clear()
        neighbor.tree_metric_state.clear()
        neighbor.last_sequence_number.clear()
        neighbor.current_sync_sn = 0
        neighbor.minimum_sequence_number = 0
        #

        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[0:5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > 0
        my_snapshot_sn = neighbor.my_snapshot_sequencer

        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, 0,
                                        sync_sequence_number=neighbor.current_sync_sn,
                                        upstream_trees=my_snapshot_mrt, master_flag=True,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
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
        if neighbor.minimum_sequence_number > neighbor_snapshot_sn:
            return
        elif neighbor.minimum_sequence_number < neighbor_snapshot_sn:
            Updated.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            return

        if master_bit and (sync_sn > 0 and neighbor.my_snapshot_sequencer == my_snapshot_sn or sync_sn==0):
            pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_snapshot_sn, sync_sequence_number=sync_sn,
                                            master_flag=False, more_flag=False, neighbor_boot_time=neighbor.time_of_boot)
            pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
            neighbor.send(pkt)
            neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)


class Master(NeighborState):
    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.current_sync_sn == 0 and neighbor.minimum_sequence_number == 0:
            neighbor.minimum_sequence_number = neighbor_snapshot_sn

        if sync_sn != neighbor.current_sync_sn:
            print("EXIT MASTER")
            return

        if neighbor.minimum_sequence_number > neighbor_snapshot_sn:
            return
        elif neighbor.minimum_sequence_number < neighbor_snapshot_sn:
            Master.new_neighbor_or_adjacency_reset(neighbor)
            return

        if master_bit and (sync_sn > 0 and neighbor.my_snapshot_sequencer == my_snapshot_sn or sync_sn == 0):
            print("ENTROU MASTER")
            neighbor.install_tree_state(tree_state)

            my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn*5:(neighbor.current_sync_sn+1)*5]
            my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5
            my_snapshot_sn = neighbor.my_snapshot_sequencer
            neighbor_sn = neighbor.minimum_sequence_number

            pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                            sync_sequence_number=neighbor.current_sync_sn,
                                            upstream_trees=my_snapshot_mrt, master_flag=False,
                                            more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
            pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
            neighbor.send(pkt)

            if sync_sn > 0 and not more_bit and not my_more_bit:
                neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_AFTER_SYNC)
                neighbor.set_sync_state(Updated)
                neighbor.clear_sync_timer()
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
        neighbor_sn = neighbor.minimum_sequence_number

        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                        sync_sequence_number=neighbor.current_sync_sn - 1,
                                        upstream_trees=my_snapshot_mrt, master_flag=False,
                                        more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
        pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
        neighbor.send(pkt)
        neighbor.set_sync_timer()


class Slave(NeighborState):
    @staticmethod
    def recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit):
        if neighbor.current_sync_sn == 0 and neighbor.minimum_sequence_number == 0:
            neighbor.minimum_sequence_number = neighbor_snapshot_sn

        if neighbor.minimum_sequence_number > neighbor_snapshot_sn:
            return
        elif neighbor.minimum_sequence_number < neighbor_snapshot_sn:
            Slave.new_neighbor_or_adjacency_reset(neighbor)
            return

        if sync_sn != neighbor.current_sync_sn:
            return

        if sync_sn == 0 and master_bit:
            print("HERE1")
            import ipaddress
            my_ip = ipaddress.ip_address(neighbor.contact_interface.get_ip())
            neighbor_ip = ipaddress.ip_address(neighbor.ip)
            if my_ip < neighbor_ip:
                print("HERE2")
                neighbor.set_sync_state(Master)
                neighbor.current_sync_sn = 0
                Master.recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit)
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
            else:
                neighbor.set_hello_hold_time(DEFAULT_HELLO_HOLD_TIME_DURING_SYNC)
                print("HERE5")
                neighbor.current_sync_sn += 1
                neighbor.install_tree_state(tree_state)

                my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[neighbor.current_sync_sn*5:(neighbor.current_sync_sn+1)*5]
                my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn*5
                my_snapshot_sn = neighbor.my_snapshot_sequencer
                neighbor_sn = neighbor.minimum_sequence_number

                pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                                sync_sequence_number=neighbor.current_sync_sn,
                                                upstream_trees=my_snapshot_mrt, master_flag=True,
                                                more_flag=my_more_bit, neighbor_boot_time=neighbor.time_of_boot)
                pkt = Packet(payload=PacketProtocolHeader(pkt_s, neighbor.my_snapshot_boot_time))
                neighbor.send(pkt)
                neighbor.set_sync_timer()

    @staticmethod
    def sync_timer_expires(neighbor):
        my_snapshot_mrt = neighbor.my_snapshot_multicast_routing_table[
                          neighbor.current_sync_sn * 5:(neighbor.current_sync_sn + 1) * 5]
        my_more_bit = len(neighbor.my_snapshot_multicast_routing_table) > neighbor.current_sync_sn * 5
        my_snapshot_sn = neighbor.my_snapshot_sequencer
        neighbor_sn = neighbor.minimum_sequence_number

        pkt_s = PacketProtocolHelloSync(my_snapshot_sn, neighbor_sn,
                                        sync_sequence_number=neighbor.current_sync_sn,
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
            neighbor.tree_state.clear()
            neighbor.tree_metric_state.clear()
            neighbor.last_sequence_number.clear()
            neighbor.current_sync_sn = 0
            neighbor.minimum_sequence_number = 0
            #

            Master.recv_sync(neighbor, tree_state, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit)
        else:
            Unknown.new_neighbor_or_adjacency_reset(neighbor)


class Neighbor:
    RETRANSMISSION_TIMEOUT = 10
    GARBAGE_COLLECT_TIMEOUT = 120

    def __init__(self, contact_interface: "InterfaceProtocol", ip, hello_hold_time: int, neighbor_time_of_boot=0, my_interface_boot_time = 0):
        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            raise Exception
        self.contact_interface = contact_interface
        self.ip = ip
        self.time_of_boot = neighbor_time_of_boot

        self.neighbor_liveness_timer = None
        self.hello_hold_time = None
        self.set_hello_hold_time(hello_hold_time)
        self.time_of_last_update = time.time()

        self.current_sync_sn = 0

        # Tree Database storage
        self.tree_state = {}
        self.tree_metric_state = {}

        # Control if received control packets should be processed
        # Used to detect msg retransmissions and out of order reception
        self.minimum_sequence_number = 0
        self.last_sequence_number = {}

        self.sync_timer = None
        self.neighbor_state = Unknown

        #(my_snapshot_sn, my_snapshot_mrt) = contact_interface.snapshot_multicast_routing_table()
        #self.my_snapshot_sequencer = my_snapshot_sn # TODO
        #self.my_snapshot_multicast_routing_table = my_snapshot_mrt.values() # TODO
        #self.my_snapshot_trees = my_snapshot_mrt.keys() # TODO
        self.my_snapshot_boot_time = my_interface_boot_time
        self.my_snapshot_sequencer = 0
        self.my_snapshot_multicast_routing_table = []
        self.my_snapshot_trees = []

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
        if state == Updated:
            import Main
            #Main.kernel.recv_ack_sync(self.ip, self.my_snapshot_trees, self.my_snapshot_sequencer, self.contact_interface)
            self.contact_interface.neighbor_finished_synchronization(self.ip, self.my_snapshot_boot_time, self.my_snapshot_sequencer)
            Main.kernel.recheck_all_trees(self.contact_interface)
            self.contact_interface.set_are_synchronizing()
            # inform about ack... nao sei se é aqui
        else:
            self.contact_interface.set_are_synchronizing()


    def install_tree_state(self, tree_state:list):
        #self.tree_state.clear()
        #self.tree_metric_state.clear()
        #self.last_sequence_number.clear()
        for t in tree_state:
            from tree.metric import AssertMetric
            tree_id = (t.source, t.group)
            self.tree_metric_state[tree_id] = AssertMetric(metric_preference=t.metric_preference, route_metric=t.metric, ip_address=self.ip)

    def remove_tree_state(self, source, group):
        self.tree_state.pop((source, group), None)

    def get_known_trees(self):
        a = set(self.tree_metric_state.keys())
        b = set(self.tree_state.keys())
        return a.union(b)

    def is_syncing(self):
        return self.neighbor_state == Slave or self.neighbor_state == Master

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
        self.my_snapshot_trees = list(my_snapshot_mrt.keys())

    def recv_hello(self, boot_time, holdtime, checkpoint_sn=0):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            return

        if self.neighbor_state == Updated:
            self.time_of_last_update = time.time()
            self.set_hello_hold_time(holdtime)
            self.set_checkpoint_sn(checkpoint_sn)
        elif holdtime==0:
            self.set_hello_hold_time(holdtime)

    def set_checkpoint_sn(self, checkpoint_sn):
        if checkpoint_sn > self.minimum_sequence_number:
            self.minimum_sequence_number = checkpoint_sn

            to_remove = {k for k,v in self.last_sequence_number.items() if v <= checkpoint_sn}
            for k in to_remove:
                self.last_sequence_number.pop(k)

    def recv_sync(self, upstream_trees, my_sn, neighbor_sn, boot_time, sync_sn, master_flag, more_flag, own_interface_boot_time):
        if boot_time < self.time_of_boot:
            return
        elif boot_time > self.time_of_boot or own_interface_boot_time > self.my_snapshot_boot_time:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            #self.start_sync_process(True)
            self.neighbor_state.new_neighbor_or_adjacency_reset(self)
            return

        self.neighbor_state.recv_sync(self, upstream_trees, my_sn, neighbor_sn, sync_sn, master_flag, more_flag)

    ################################################################################################
    def get_tree_state(self, tree):
        if self.neighbor_state != Updated:
            return (False, None)
        else:
            upstream_state = self.tree_metric_state.get(tree, None)
            interest_state = False
            if upstream_state is None:
                #interest_state = self.tree_state.get(tree, True)
                interest_state = self.tree_state.get(tree, globals.INITIAL_FLOOD_ENABLED)
            print("INTEREST NEIGHBOR ", self.ip, ":", interest_state)
            print("UPSTREAM NEIGHBOR ", self.ip, ":", upstream_state)
            return (interest_state, upstream_state)

    def recv_reliable_packet(self, sn, tree, boot_time):
        if self.neighbor_state != Updated:
            # do not interpret message during sync
            return False

        if boot_time < self.time_of_boot:
            return False
        elif boot_time > self.time_of_boot:
            self.time_of_boot = boot_time
            self.minimum_sequence_number = 0
            self.start_sync_process()
            return False

        last_received_sn = self.last_sequence_number.get(tree, 0)

        if sn < self.minimum_sequence_number:
            # dont deliver to application
            print("RCVD ", sn)
            print("MSN ", self.minimum_sequence_number)

            return False
        elif sn >= last_received_sn:
            (source, group) = tree
            ack = PacketProtocolAck(source, group, sn, boot_time)
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

    ################################################################################################

    def set_hello_hold_time(self, hello_hold_time: int):
        self.hello_hold_time = hello_hold_time
        if self.neighbor_liveness_timer is not None:
            self.neighbor_liveness_timer.cancel()

        if hello_hold_time == HELLO_HOLD_TIME_TIMEOUT:
            self.remove()
        elif hello_hold_time != HELLO_HOLD_TIME_NO_TIMEOUT:
            self.neighbor_liveness_timer = Timer(hello_hold_time, self.remove)
            self.neighbor_liveness_timer.start()
        else:
            self.neighbor_liveness_timer = None

    def remove(self):
        with self.contact_interface.neighbors_lock:
            print('HELLO TIMER EXPIRED... remove neighbor')
            if self.neighbor_liveness_timer is not None:
                self.neighbor_liveness_timer.cancel()

            self.clear_sync_timer()

            self.tree_state.clear()
            self.tree_metric_state.clear()
            self.last_sequence_number.clear()

            self.contact_interface.remove_neighbor(self.ip)
