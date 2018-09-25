from abc import ABCMeta
from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .KernelEntry import KernelEntry


class TreeStateABC(metaclass=ABCMeta):
    @staticmethod
    def is_active():
        """
        Verify if the interface state is Active
        """
        return False

    @staticmethod
    def is_inactive():
        """
        Verify if the interface state is Active
        """
        return False

    @staticmethod
    def is_unknown():
        """
        Verify if the interface state is Active
        """
        return False

    @staticmethod
    def transition_to_active(kernel_entry: 'KernelEntry'):
        """
        Tree transitioned to Active state
        """
        if kernel_entry.is_tree_active():
            return
        kernel_entry.set_tree_state(TreeState.Active)
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_active()
        kernel_entry.change()
        kernel_entry.evaluate_in_tree_change()

    @staticmethod
    def transition_to_inactive(kernel_entry: 'KernelEntry'):
        """
        Tree transitioned to Inactive state
        """
        if kernel_entry.is_tree_inactive():
            return
        kernel_entry.set_tree_state(TreeState.Inactive)
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_inactive()
        kernel_entry.change()
        kernel_entry.evaluate_in_tree_change()

    @staticmethod
    def transition_to_unknown(kernel_entry: 'KernelEntry'):
        """
        Tree transitioned to Unknown state
        """
        if kernel_entry.is_tree_unknown():
            return
        kernel_entry.set_tree_state(TreeState.Unknown)
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_unknown()
        kernel_entry.remove_entry()


class ActiveTree(TreeStateABC):
    @staticmethod
    def is_active():
        """
        Verify if the interface state is Active
        """
        return True

    def __str__(self):
        return "Active"


class InactiveTree(TreeStateABC):
    @staticmethod
    def is_inactive():
        """
        Verify if the interface state is Inactive
        """
        return True

    def __str__(self):
        return "Inactive"


class UnknownTree(TreeStateABC):
    @staticmethod
    def is_unknown():
        """
        Verify if the interface state is Unknown
        """
        return True

    def __str__(self):
        return "Unknown"


class TreeState:
    Active = ActiveTree()
    Inactive = InactiveTree()
    Unknown = UnknownTree()
