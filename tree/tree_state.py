from utils import TYPE_CHECKING

if TYPE_CHECKING:
    from .KernelEntry import KernelEntry


class TreeState:
    @staticmethod
    def is_active():
        return False

    @staticmethod
    def is_inactive():
        return False

    @staticmethod
    def is_unknown():
        return False

    @staticmethod
    def transition_to_active(kernel_entry: 'KernelEntry'):
        if kernel_entry._tree_state == ActiveTree:
            return
        kernel_entry._tree_state = ActiveTree
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_active()
        kernel_entry.change()
        kernel_entry.evaluate_in_tree_change()

    @staticmethod
    def transition_to_inactive(kernel_entry: 'KernelEntry'):
        if kernel_entry._tree_state == InactiveTree:
            return
        kernel_entry._tree_state = InactiveTree
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_inactive()
        kernel_entry.change()
        kernel_entry.evaluate_in_tree_change()

    @staticmethod
    def transition_to_unknown(kernel_entry: 'KernelEntry'):
        if kernel_entry._tree_state == UnknownTree:
            return
        kernel_entry._tree_state = UnknownTree
        for interface in kernel_entry.interface_state.values():
            interface.tree_transition_to_unknown()
        kernel_entry.remove_entry()


class ActiveTree(TreeState):
    @staticmethod
    def is_active():
        return True


class InactiveTree(TreeState):
    @staticmethod
    def is_inactive():
        return True


class UnknownTree(TreeState):
    @staticmethod
    def is_unknown():
        return True
