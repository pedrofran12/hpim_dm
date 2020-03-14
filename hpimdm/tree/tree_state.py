from abc import ABCMeta
from hpimdm.utils import TYPE_CHECKING

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
    def is_unsure():
        """
        Verify if the interface state is Unsure
        """
        return False

    @staticmethod
    def is_inactive():
        """
        Verify if the interface state is Inactive
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
    def transition_to_unsure(kernel_entry: 'KernelEntry'):
        """
        Tree transitioned to Unsure state
        """
        if kernel_entry.is_tree_unsure():
            return
        kernel_entry.set_tree_state(TreeState.Unsure)
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_unsure()
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


class UnsureTree(TreeStateABC):
    @staticmethod
    def is_unsure():
        """
        Verify if the interface state is Unsure
        """
        return True

    def __str__(self):
        return "Unsure"


class InactiveTree(TreeStateABC):
    @staticmethod
    def is_inactive():
        """
        Verify if the interface state is Inactive
        """
        return True

    def __str__(self):
        return "Inactive"


class TreeState:
    Active = ActiveTree()
    Unsure = UnsureTree()
    Inactive = InactiveTree()
