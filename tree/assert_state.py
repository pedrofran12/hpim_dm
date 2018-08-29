from abc import ABCMeta, abstractmethod


class SFMRAssertABC(metaclass=ABCMeta):
    @staticmethod
    @abstractmethod
    def is_assert_winner():
        raise Exception


class SFMRAssertWinner(SFMRAssertABC):
    @staticmethod
    def is_assert_winner():
        """
        Determine if this state is AssertWinner
        """
        return True

    def __str__(self):
        return "AssertWinner"


class SFMRAssertLoser(SFMRAssertABC):
    @staticmethod
    def is_assert_winner():
        """
        Determine if this state is AssertWinner
        """
        return False

    def __str__(self):
        return "AssertLoser"


class AssertState():
    Winner = SFMRAssertWinner()
    Loser = SFMRAssertLoser()
