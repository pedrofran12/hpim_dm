# New Protocol

We have specified and implemented a new multicast routing protocol.
This repository stores the implementation of this protocol. The implementation is written in Python language and is destined to Linux systems.


# Requirements

 - Linux machine
 - Python3 (we have written all code to be compatible with at least Python v3.2)
-  pip (to install all dependencies)


# Installation
You may need sudo permitions, in order to run this protocol. This is required because we use raw sockets to exchange control messages. For this reason, some sockets to work properly need to have super user permissions.

First clone this repository:
  `git clone https://github.com/pedrofran12/pim.git`

Then enter in the cloned repository and install all dependencies:
   `pip3 install -r requirements.txt`
 
And thats it :D


# Run protocol

In order to interact with the protocol you need to allways execute Run.py file. You can interact with the protocol by executing this file and specifying a command and corresponding arguments:

   `sudo python3 Run.py -COMMAND ARGUMENTS`

In order to determine which commands are available you can call the help command:
	`sudo python3 Run.py -h`
    or
	`sudo python3 Run.py --help`

In order to start the protocol you first need to explicitly start it. This will start a daemon process, which will be running in the background. The command is the following:
	`sudo python3 Run.py -start`

Then you can enable the protocol in specific interfaces. You need to specify which interfaces will have IGMP enabled and which interfaces will have the protocol enabled.
To have a given interface being monitored by the protocol (to exchange control packets with it), you need to run the following command:
	`sudo python3 Run.py -ai INTERFACE_NAME`

To have a given interface being monitored by IGMP (to monitor the interest of directly connected hosts), you need to run the following command:
	`sudo python3 Run.py -aiigmp INTERFACE_NAME`

To remove a previously added interface, you need run the following commands:
To remove a previously added protocol interface:
	`sudo python3 Run.py -ri INTERFACE_NAME`

To remove a previously added IGMP interface:
	`sudo python3 Run.py -riigmp INTERFACE_NAME`

If you want to stop the protocol process, and stop the daemon process, you need to explicitly run this command:
	`sudo python3 Run.py -stop`



## Commands for monitoring the protocol process
We have built some list commands that can be used to check the "internals" of the protocol.

 - List neighbors: 
	 Verify neighbors that have established a neighborhood relationship
	`sudo python3 Run.py -ln`

 - List sequence numbers:
    Verify all stored sequence numbers 
	`sudo python3 Run.py -lsn`

 - List neighbor state (Upstream/NoUpstream and Interest/NoInterest):
    Verify all state regarding each neighbor, whether they are Upstream or NotUpstream and in the latter whether they are Interested or NotInterested in receiving data packets
	`sudo python3 Run.py -lns`

 - List state machines and corresponding states of all trees that are being monitored, for each interface:
    List all state machines and corresponding state of all trees that are being monitored. Also list IGMP state for each group being monitored.
	`sudo python3 Run.py -ls`

 - Multicast Routing Table:
   List Linux Multicast Routing Table (equivalent to ip mroute -show)
	`sudo python3 Run.py -mr`

## Change settings

 - Flooding Initial Data:
 Control flooding behavior (whether to flood or not packets during the broadcast tree formation)
	`sudo python3 Run.py -fid`


Files tree/protocol_globals.py and igmp/igmp_globals.py store all timer values and some configurations regarding IGMP and the new protocol. If you want to tune the protocol, you can change the values of these files. These configurations are used by all interfaces, meaning that there is no tuning per interface.
