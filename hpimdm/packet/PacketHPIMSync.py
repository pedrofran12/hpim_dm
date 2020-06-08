import json
import struct
import socket

from .PacketHPIMHelloOptions import PacketHPIMHelloOptions, PacketHPIMHelloOptionsJson
###########################################################################################################
# JSON FORMAT
###########################################################################################################
class PacketHPIMSyncEntryJson():
    def __init__(self, source, group, metric_preference, metric):
        self.source = source
        self.group = group
        self.metric = metric
        self.metric_preference = metric_preference

    def bytes(self):
        """
        Obtain entry of Protocol Sync in a format to be transmitted (JSON)
        """
        msg = {"SOURCE": self.source,
               "GROUP": self.group,
               "METRIC": self.metric,
               "METRIC_PREFERENCE": self.metric_preference,
              }
        return msg

    @staticmethod
    def parse_bytes(data: bytes):
        """
        Parse received entry of Protocol Sync Packet from JSON format
        and convert it into ProtocolSyncEntry object and PacketProtocolSyncEntries
        """
        source = data["SOURCE"]
        group = data["GROUP"]
        metric = data["METRIC"]
        metric_preference = data["METRIC_PREFERENCE"]
        return PacketHPIMSyncEntryJson(source, group, metric_preference, metric)

    def __len__(self):
        return len(json.dumps(self.bytes()).encode())


class PacketHPIMSyncJson():
    PIM_TYPE = "SYNC"

    def __init__(self, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, upstream_trees=[],
                 master_flag=False, more_flag=False, neighbor_boot_time=0):
        self.sync_sequence_number = sync_sn
        self.my_snapshot_sn = my_snapshot_sn
        self.neighbor_snapshot_sn = neighbor_snapshot_sn
        self.neighbor_boot_time = neighbor_boot_time
        self.upstream_trees = upstream_trees
        self.master_flag = master_flag
        self.more_flag = more_flag
        self.options = {}

    def add_hello_option(self, option: 'PacketHPIMHelloOptions'):
        self.options[option.type] = option

    def get_hello_options(self):
        return self.options

    def bytes(self) -> bytes:
        """
        Obtain Protocol Sync Packet in a format to be transmitted (JSON)
        """
        trees = []
        for entry in self.upstream_trees:
            trees.append(entry.bytes())

        msg = {"SYNC_SN": self.sync_sequence_number,
               "MY_SNAPSHOT_SN": self.my_snapshot_sn,
               "NEIGHBOR_SNAPSHOT_SN": self.neighbor_snapshot_sn,
               "NEIGHBOR_BOOT_TIME": self.neighbor_boot_time,
               "TREES": trees,
               "MASTER_FLAG": self.master_flag,
               "MORE_FLAG": self.more_flag,
               "HELLO_OPTIONS": {}
              }
        for hello_option in self.options.values():
            msg["HELLO_OPTIONS"].update(hello_option.bytes())

        return msg

    def parse_bytes(data: bytes):
        """
        Parse received Protocol Sync Packet and all its entries from JSON format
        and convert it into ProtocolSync object and PacketProtocolSyncEntries
        """
        trees = []
        for entry in data["TREES"]:
            trees.append(PacketHPIMSyncEntryJson.parse_bytes(entry))

        sync_sn = data["SYNC_SN"]
        my_snapshot_sn = data["MY_SNAPSHOT_SN"]
        neighbor_snapshot_sn = data["NEIGHBOR_SNAPSHOT_SN"]
        neighbor_boot_time = data["NEIGHBOR_BOOT_TIME"]
        master_flag = data["MASTER_FLAG"]
        more_flag = data["MORE_FLAG"]
        hello_options = data["HELLO_OPTIONS"]
        sync_msg = PacketHPIMSyncJson(my_snapshot_sn, neighbor_snapshot_sn, sync_sn, trees, master_flag,
                                      more_flag, neighbor_boot_time)
        for (key, value) in hello_options.items():
            option = PacketHPIMHelloOptionsJson.parse_bytes((key, value))
            sync_msg.add_hello_option(option)

        return sync_msg


###########################################################################################################
# BINARY FORMAT
###########################################################################################################
'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                        Tree Source IP                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         Tree Group IP                         |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       Metric Preference                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                            Metric                             |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketHPIMSyncEntry:
    PIM_HDR_SYNC_ENTRY = "! 4s 4s L L"
    PIM_HDR_SYNC_ENTRY_LEN = struct.calcsize(PIM_HDR_SYNC_ENTRY)
    FAMILY = socket.AF_INET

    def __init__(self, source, group, metric_preference, metric):
        if type(source) not in (str, bytes) or type(group) not in (str, bytes):
            raise Exception
        if type(source) is bytes:
            source = socket.inet_ntop(self.FAMILY, source)
        if type(group) is bytes:
            group = socket.inet_ntop(self.FAMILY, group)

        self.source = source
        self.group = group
        self.metric = metric
        self.metric_preference = metric_preference

    def __len__(self):
        return self.PIM_HDR_SYNC_ENTRY_LEN

    def bytes(self):
        """
        Obtain entry of Protocol Sync in a format to be transmitted (binary)
        """
        msg = struct.pack(self.PIM_HDR_SYNC_ENTRY, socket.inet_pton(self.FAMILY, self.source),
                          socket.inet_pton(self.FAMILY, self.group), self.metric_preference, self.metric)
        return msg

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received entry of Protocol Sync Packet from binary format
        and convert it into ProtocolSyncEntry object and PacketProtocolSyncEntries
        """
        (source, group, metric_preference, metric) = struct.unpack(cls.PIM_HDR_SYNC_ENTRY,
                                                                   data[:cls.PIM_HDR_SYNC_ENTRY_LEN])
        return cls(source, group, metric_preference, metric)


class PacketHPIMSyncEntry_v6(PacketHPIMSyncEntry):
    PIM_HDR_SYNC_ENTRY = "! 16s 16s L L"
    PIM_HDR_SYNC_ENTRY_LEN = struct.calcsize(PIM_HDR_SYNC_ENTRY)
    FAMILY = socket.AF_INET6

    def __init__(self, source, group, metric_preference, metric):
        super().__init__(source, group, metric_preference, metric)


'''
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                         MySnapshotSN                          |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                      NeighborSnapshotSN                       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                       NeighborBootTime                        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|M|m|                        Sync SN                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|     Trees (equivalent to multiple IamUpstream messages)       |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
'''
class PacketHPIMSync:
    PIM_TYPE = 1

    PIM_HDR_INSTALL_WITHOUT_TREES = "! L L L L"
    PIM_HDR_INSTALL_WITHOUT_TREES_LEN = struct.calcsize(PIM_HDR_INSTALL_WITHOUT_TREES)

    def __init__(self, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, upstream_trees,
                 master_flag=False, more_flag=False, neighbor_boot_time=0):
        self.my_snapshot_sn = my_snapshot_sn
        self.neighbor_snapshot_sn = neighbor_snapshot_sn
        self.neighbor_boot_time = neighbor_boot_time
        self.sync_sequence_number = sync_sn
        self.master_flag = master_flag
        self.more_flag = more_flag
        self.upstream_trees = upstream_trees
        self.options = {}

    def add_tree(self, t):
        self.upstream_trees.append(t)

    def add_hello_option(self, option: 'PacketHPIMHelloOptions'):
        self.options[option.TYPE] = option

    def get_hello_options(self):
        return self.options

    def bytes(self) -> bytes:
        """
        Obtain entry of Protocol Sync in a format to be transmitted (binary)
        """
        flags_and_sync_sn = (self.master_flag << 31) | (self.more_flag << 30) | self.sync_sequence_number

        msg = struct.pack(self.PIM_HDR_INSTALL_WITHOUT_TREES, self.my_snapshot_sn,
                          self.neighbor_snapshot_sn, self.neighbor_boot_time, flags_and_sync_sn)
        if self.more_flag:
            for t in self.upstream_trees:
                msg += t.bytes()
        else:
            for option in self.options.values():
                msg += option.bytes()
        return msg

    def __len__(self):
        return len(self.bytes())

    @staticmethod
    def _get_entry_object():
        return PacketHPIMSyncEntry

    @classmethod
    def parse_bytes(cls, data: bytes):
        """
        Parse received Protocol Sync Packet and all its entries from binary format
        and convert it into ProtocolSync object and PacketProtocolSyncEntries
        """
        (my_snapshot_sn, neighbor_snapshot_sn, neighbor_boot_time, flags_and_sync_sn) = \
            struct.unpack(cls.PIM_HDR_INSTALL_WITHOUT_TREES,
                          data[:cls.PIM_HDR_INSTALL_WITHOUT_TREES_LEN])

        sync_sn = flags_and_sync_sn & 0x3FFFFFFF
        master_flag = flags_and_sync_sn >> 31
        more_flag = (flags_and_sync_sn & 0x4FFFFFFF) >> 30
        data = data[cls.PIM_HDR_INSTALL_WITHOUT_TREES_LEN:]
        sync_msg = cls(my_snapshot_sn, neighbor_snapshot_sn, sync_sn, [], master_flag=master_flag,
                       more_flag=more_flag, neighbor_boot_time=neighbor_boot_time)
        if more_flag:
            while data != b'':
                tree_msg = cls._get_entry_object().parse_bytes(data)

                sync_msg.add_tree(tree_msg)
                data = data[len(tree_msg):]
        else:
            while data != b'':
                option = PacketHPIMHelloOptions.parse_bytes(data)
                option_length = len(option)
                data = data[option_length:]
                sync_msg.add_hello_option(option)
        return sync_msg


class PacketHPIMSync_v6(PacketHPIMSync):
    def __init__(self, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, upstream_trees,
                 master_flag, more_flag, neighbor_boot_time):
        super().__init__(my_snapshot_sn, neighbor_snapshot_sn, sync_sn, upstream_trees,
                         master_flag, more_flag, neighbor_boot_time)

    @staticmethod
    def _get_entry_object():
        return PacketHPIMSyncEntry_v6
