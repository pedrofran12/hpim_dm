# Allow flood initial data packet even when there is no information regarding
# Upstream neighbors
INITIAL_FLOOD_ENABLED = True
INITIAL_FLOOD_TIME = 15

MSG_FORMAT = "BINARY"  # other msg format is JSON

# Originator will stop considering the tree Active after not hearing data packets
# from the source after SOURCE_LIFETIME SECONDS
SOURCE_LIFETIME = 210

# Periodicity for message retransmission
MESSAGE_RETRANSMISSION_TIME = 10


HELLO_HOLD_TIME_TIMEOUT = 0

# Control fragmentation of Sync messages
# Number of trees per Sync message
# If zero, use information from MTU of interface, otherwise only include a positive given number of trees per Sync message
SYNC_FRAGMENTATION_MSG = 0


# Number of ACKs that must be missed in order to declare a neighbor to have failed
# Use a number HIGHER than 1!!
ACK_FAILURE_THRESHOLD = 3


# Time to wait for a Sync message
# If Synchronization does not make progress, retransmit previous Sync message
SYNC_RETRANSMISSION_TIME = 3


# When an AW loses an assert and becomes AL, it can hold its forwarding state for a given ammount of time to prevent
# the loss of data packes (the new AW may not be receiving multicast tree from its parent yet causing the interest
# signaling to be propageted upwards the tree).
# If enabled this prevents loss of data packets after the AW is replaced, but duplications may occur for a small
#   amount of time (the AW and the AL may both forwarding packets at the same time during AL_HOLD_FORWARDING_STATE_TIME)
# If disabled the duplication of data packets does not occur but loss of packets may occur
AL_HOLD_FORWARDING_STATE_ENABLED = True
AL_HOLD_FORWARDING_STATE_TIME = 2
