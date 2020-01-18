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
