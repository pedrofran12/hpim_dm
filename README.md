# HPIM-DM

We have specified and implemented a multicast routing protocol named HPIM-DM (Hard-state Protocol Independent Multicast - Dense Mode).
This repository stores the implementation of this protocol. The implementation is written in Python language and is destined to Linux systems.


# Documents detailing this work

 - [HPIM-DM state machines](./docs/HPIMStateMachines.pdf)
 - [Python implementation of IGMPv2, PIM-DM and HPIM-DM](./docs/PythonImplementations.pdf)
 - [Test to Python implementation of IGMPv2, PIM-DM, and HPIM-DM](./docs/PythonTests.pdf)
 - [SPIN/Promela correctness tests of HPIM-DM](./docs/CorrectnessTests.pdf)


# Requirements

 - Linux machine
 - Python3 (we have written all code to be compatible with at least Python v3.2)
 - pip (to install all dependencies)


# Installation
You may need sudo permissions, in order to run this protocol. This is required because we use raw sockets to exchange control messages. For this reason, some sockets to work properly need to have super user permissions.

First clone this repository:
  `git clone https://github.com/pedrofran12/hpim_dm.git`

Then enter in the cloned repository and install the protocol:
   `sudo python3 setup.py install`

And that's it :D


# Run HPIM-DM

To interact with the protocol you need to execute the `hpim-dm` command. You may need to specify a command and corresponding arguments:

   `hpim-dm -COMMAND ARGUMENTS`

In order to determine which commands are available you can call the help command:

   `hpim-dm -h`

or

   `hpim-dm --help`

In order to start the protocol you first need to explicitly start it. This will start a daemon process, which will be running in the background. The command is the following:

   `sudo hpim-dm -start`

Then you can enable the protocol in specific interfaces. You need to specify which interfaces will have IGMP enabled and which interfaces will have HPIM-DM enabled.
* To have a given interface being monitored by HPIM-DM (to exchange control packets with it), you need to run the following command:

	`sudo hpim-dm -ai INTERFACE_NAME`

* To have a given interface being monitored by IGMP (to monitor the interest of directly connected hosts), you need to run the following command:

	`sudo hpim-dm -aiigmp INTERFACE_NAME`

To remove a previously added interface, you need to run the following commands:

* To remove a previously added HPIM-DM interface:

	`sudo hpim-dm -ri INTERFACE_NAME`

* To remove a previously added IGMP interface:

	`sudo hpim-dm -riigmp INTERFACE_NAME`

If you want to stop the protocol process, and stop the daemon process, you need to explicitly run this command:

   `sudo hpim-dm -stop`



## Commands for monitoring the protocol process
We have built some list commands that can be used to check the "internals" of the protocol.

 - List neighbors:

	 Verify neighbors that have established a neighborhood relationship

	`sudo hpim-dm -ln`

 - List sequence numbers:

    Verify all stored sequence numbers

	`sudo hpim-dm -lsn`

 - List neighbor state (UPSTREAM/NOT UPSTREAM and INTERESTED/NOT INTERESTED):

    Verify all state regarding each neighbor, whether they are UPSTREAM or NOT UPSTREAM and in the latter whether they are INTERESTED or NOT INTERESTED in receiving data packets

	`sudo hpim-dm -lns`

 - List state machines and corresponding states of all trees that are being monitored, for each interface:

    List all state machines and corresponding state of all trees that are being monitored. Also list IGMP state for each group being monitored.

	`sudo hpim-dm -ls`

 - Multicast Routing Table:

   List Linux Multicast Routing Table (equivalent to ip mroute -show)

	`sudo hpim-dm -mr`

## Change settings

 - Flooding Initial Data:

 Control flooding behavior (whether to flood or not packets during the broadcast tree formation)

   `sudo hpim-dm -fid`


Files tree/protocol_globals.py and igmp/igmp_globals.py store all timer values and some configurations regarding IGMP and the new protocol. If you want to tune the protocol, you can change the values of these files. These configurations are used by all interfaces, meaning that there is no tuning per interface.
