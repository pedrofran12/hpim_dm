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