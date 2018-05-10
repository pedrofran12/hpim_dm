from abc import ABCMeta, abstractmethod

class SFMRAssertABC(metaclass=ABCMeta):
    @staticmethod
    @abstractmethod
    def is_assert_winner():
        raise Exception


class SFMRAssertWinner(SFMRAssertABC):
    @staticmethod
    def is_assert_winner():
        return True


class SFMRAssertLoser(SFMRAssertABC):
    @staticmethod
    def is_assert_winner():
        return False


class AssertState():
    Winner = SFMRAssertWinner()
    Loser = SFMRAssertLoser()
