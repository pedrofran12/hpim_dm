from abc import ABCMeta, abstractmethod


class LocalMembershipStateABC(metaclass=ABCMeta):
    @staticmethod
    @abstractmethod
    def has_members():
        """
        Determine if this state considers to have hosts interested in receiving data packets
        """
        raise NotImplementedError


class NoInfo(LocalMembershipStateABC):
    @staticmethod
    def has_members():
        """
        Determine if this state considers to have hosts interested in receiving data packets
        """
        return False

    def __str__(self):
        return "NoInfo"


class Include(LocalMembershipStateABC):
    @staticmethod
    def has_members():
        """
        Determine if this state considers to have hosts interested in receiving data packets
        """
        return True

    def __str__(self):
        return "Include"


class LocalMembership():
    NoInfo = NoInfo()
    Include = Include()
