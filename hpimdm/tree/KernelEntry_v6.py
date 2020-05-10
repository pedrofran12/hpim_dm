from hpimdm import Main
from .KernelEntry import KernelEntryNonOriginator, KernelEntryOriginator


class KernelEntryNonOriginator_v6(KernelEntryNonOriginator):
    def __init__(self, source_ip: str, group_ip: str, upstream_state_dic, interest_state_dic):
        super().__init__(source_ip, group_ip, upstream_state_dic, interest_state_dic)

    def get_outbound_interfaces_indexes(self):
        """
        Get OIL of this tree
        """
        outbound_indexes = [0] * 8
        for (index, state) in self.interface_state.items():
            outbound_indexes[index // 32] |= state.is_forwarding() << (index % 32)
        return outbound_indexes

    @staticmethod
    def get_interface_name(interface_id):
        """
        Get name of interface from vif id
        """
        return Main.kernel_v6.vif_index_to_name_dic[interface_id]

    @staticmethod
    def get_interface(interface_id):
        """
        Get HPIM interface from interface id
        """
        interface_name = KernelEntryNonOriginator_v6.get_interface_name(interface_id)
        return Main.interfaces_v6.get(interface_name, None)

    @staticmethod
    def get_membership_interface(interface_id):
        """
        Get MLD interface from interface id
        """
        interface_name = KernelEntryNonOriginator_v6.get_interface_name(interface_id)
        return Main.mld_interfaces.get(interface_name, None)  # type: InterfaceMLD

    @staticmethod
    def get_kernel():
        """
        Get kernel
        """
        return Main.kernel_v6


class KernelEntryOriginator_v6(KernelEntryOriginator):
    def __init__(self, source_ip: str, group_ip: str, upstream_state_dic, interest_state_dic):
        super().__init__(source_ip, group_ip, upstream_state_dic, interest_state_dic)

    def get_outbound_interfaces_indexes(self):
        """
        Get OIL of this tree
        """
        outbound_indexes = [0] * 8
        for (index, state) in self.interface_state.items():
            outbound_indexes[index // 32] |= state.is_forwarding() << (index % 32)
        return outbound_indexes

    @staticmethod
    def get_interface_name(interface_id):
        """
        Get name of interface from vif id
        """
        return Main.kernel_v6.vif_index_to_name_dic[interface_id]

    @staticmethod
    def get_interface(interface_id):
        """
        Get HPIM interface from interface id
        """
        interface_name = KernelEntryOriginator_v6.get_interface_name(interface_id)
        return Main.interfaces_v6.get(interface_name, None)

    @staticmethod
    def get_membership_interface(interface_id):
        """
        Get MLD interface from interface id
        """
        interface_name = KernelEntryOriginator_v6.get_interface_name(interface_id)
        return Main.mld_interfaces.get(interface_name, None)  # type: InterfaceMLD

    @staticmethod
    def get_kernel():
        """
        Get kernel
        """
        return Main.kernel_v6
