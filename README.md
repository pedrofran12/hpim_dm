# HPIM-DM

We have specified and implemented a multicast routing protocol named HPIM-DM (Hard-state Protocol Independent Multicast - Dense Mode).
This repository stores the implementation of this protocol. The implementation is written in Python language and is destined to Linux systems.


# Documents detailing this work

 - [HPIM-DM state machines](https://github.com/pedrofran12/hpim_dm/tree/master/docs/HPIMStateMachines.pdf)
 - [Python implementation of IGMPv2, PIM-DM and HPIM-DM](https://github.com/pedrofran12/hpim_dm/tree/master/docs/PythonImplementations.pdf)
 - [Test to Python implementation of IGMPv2, PIM-DM, and HPIM-DM](https://github.com/pedrofran12/hpim_dm/tree/master/docs/PythonTests.pdf)
 - [SPIN/Promela correctness tests of HPIM-DM](https://github.com/pedrofran12/hpim_dm/tree/master/docs/CorrectnessTests.pdf)


# Requirements

 - Linux machine
 - Python3 (we have written all code to be compatible with at least Python v3.2)
 - pip (to install all dependencies)
 - tcpdump


# Installation

  ```
  pip3 install hpim-dm
  ```

# Run HPIM-DM

You may need sudo permissions, in order to run this protocol. This is required because we use raw sockets to exchange control messages. For this reason, some sockets to work properly need to have super user permissions.

To interact with the protocol you need to execute the `hpim-dm` command. You may need to specify a command and corresponding arguments:

   `hpim-dm -COMMAND ARGUMENTS`


#### Start protocol process

In order to start the protocol you first need to explicitly start it. This will start a daemon process, which will be running in the background. The command is the following:

   ```
   sudo hpim-dm -start
   ```


#### Add interface

After starting the protocol process you can enable the protocol in specific interfaces. You need to specify which interfaces will have IGMP enabled and which interfaces will have HPIM-DM enabled.
* To have a given interface being monitored by HPIM-DM (to exchange control packets with it), you need to run the following command:

	```
  sudo hpim-dm -ai INTERFACE_NAME
  ```

* To have a given interface being monitored by IGMP (to monitor the interest of directly connected hosts), you need to run the following command:

	```
  sudo hpim-dm -aiigmp INTERFACE_NAME
  ```


#### Remove interface

To remove a previously added interface, you need to run the following commands:

* To remove a previously added HPIM-DM interface:

	```
  sudo hpim-dm -ri INTERFACE_NAME
  ```

* To remove a previously added IGMP interface:

	```
  sudo hpim-dm -riigmp INTERFACE_NAME
  ```


#### Stop protocol process

If you want to stop the protocol process, and stop the daemon process, you need to explicitly run this command:

   ```
   sudo hpim-dm -stop
   ```


## Security

HPIM-DM offers integrity, authentication and freshness guarantees on control messages. These guarantees are achieved by appending an HMAC on all control messages and by having monotonically increasing sequence numbers.

All control messages carry a Security Identifier, which is a number that identifies the algorithm and key used on the HMAC calculation (same as Key ID on OSPF). All routers connected to a link must agree on the security identifier, algorithm and key. This security is per interface meaning that different interfaces can have different security identifiers, algorithms and keys (which is highly **recommended**).

 - #### List security algorithms:

   List all available hash algorithms that can be used to create the HMAC.

   ```
   sudo hpim-dm -lsec
   ```

 - #### Add security on interface:

   Enable security on HPIM-DM interface named INTERFACE_NAME. The SECURITY_IDENTIFIER is a number and identifies the algorithm and key of the HMAC. To check the available algorithms run -lsec.

   ```
   sudo hpim-dm -aisec INTERFACE_NAME SECURITY_IDENTIFIER SECURITY_ALGORITHM SECURITY_KEY
   ```

 - #### Remove security from interface:

   Disable security identified by SECURITY_IDENTIFIER from HPIM-DM interface named INTERFACE_NAME.

   ```
   sudo hpim-dm -risec INTERFACE_NAME SECURITY_IDENTIFIER
   ```



## Commands for monitoring the protocol process
We have built some list commands that can be used to check the "internals" of the protocol.

 - #### List interfaces:

	 Show all router interfaces and which ones have HPIM-DM and IGMP enabled. For IGMP enabled interfaces check the IGMP Querier state. For HPIM enabled interfaces check security settings.

   ```
   sudo hpim-dm -li
   ```

 - #### List neighbors:

	 Verify neighbors that have established a neighborhood relationship.

   ```
   sudo hpim-dm -ln
   ```

 - #### List sequence numbers:

    Verify all stored sequence numbers.

   ```
   sudo hpim-dm -lsn
   ```

 - #### List neighbor state:

    Verify all state regarding each neighbor, whether they are UPSTREAM or NOT UPSTREAM and in the latter whether they are INTERESTED or NOT INTERESTED in receiving data packets.

   ```
   sudo hpim-dm -lns
   ```

 - #### List state machines:

    List all state machines and corresponding state of all trees that are being monitored. Also list IGMP state for each group being monitored.

   ```
   sudo hpim-dm -ls
   ```

 - #### Multicast Routing Table:

   List Linux Multicast Routing Table (equivalent to `ip mroute -show`)

   ```
   sudo hpim-dm -mr
   ```


## Change settings

 - #### Flooding Initial Data:

   Control flooding behavior (whether to flood or not data packets during the broadcast tree formation)

   ```
   sudo hpim-dm -fid
   ```

 - #### Hold Forwarding State:

   This setting allows during an AW replacement (for example due to RPC changes) for the previous AW to hold its forwarding state for a small amount of time. This way it is possible to prevent loss of data packets during this event, however it may introduce traffic duplication (while the new and the previous AW both forward traffic). By default this setting is enabled with a time period of 2 seconds.

   ```
   sudo hpim-dm -hfs
   ```

Files tree/protocol_globals.py and igmp/igmp_globals.py store all timer values and some configurations regarding IGMPv2 and HPIM-DM. If you want to tune the protocol, you can change the values of these files. These configurations are used by all interfaces, meaning that there is no tuning per interface.



## Help command
In order to determine which commands and corresponding arguments are available you can call the help command:

  ```
  hpim-dm -h
  ```

  or

  ```
  hpim-dm --help
  ```

## Wireshark dissector

We have created a wireshark dissector in order to interpret HPIM-DM control packets using Wireshark. The plugin can be found on our [dissector branch](https://github.com/pedrofran12/hpim_dm/tree/dissector).


## Tests

We have performed tests to our specification and implementation. You can check on the corresponding branches:

- [promela](https://github.com/pedrofran12/hpim_dm/tree/promela) - Validation of correctness properties, through model checking, of different HPIM-DM state machines using Promela and Spin.
- [Test_NewProtocol_BroadcastTree](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_BroadcastTree) - Topology used to test our implementation regarding the creation and maintenance of the broadcast tree.
- [Test_NewProtocol_Sync_Without_Trees](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_Sync_Without_Trees) - Topology used to test the implementation of HPIM-DM neighbor discovery and synchronization without trees established on the network.
- [Test_NewProtocol_Sync_With_Trees](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_Sync_With_Trees) - Topology used to test the implementation of HPIM-DM neighbor discovery and synchronization mechanism with trees already established on the network.
- [Test_NewProtocol_Assert](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_Assert) - Topology used to test the implementation of the HPIM-DM AssertWinner election.
- [Test_NewProtocol_Interest](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_Interest) - Topology used to test HPIM-DM implementation regarding the forwarding decision of routers by having multicast interest changes.
- [Test_NewProtocol_Loop](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_Loop) - Topology used to test the avoidance of trees being maintained indefinitely in the presence of loops on HPIM-DM.
- [Test_NewProtocol_Source_Loop](https://github.com/pedrofran12/hpim_dm/tree/Test_NewProtocol_Source_Loop) - Topology used to test the prevention of data packets being looped when a originator router has multiple interfaces directly connected to the source.
- [Test_IGMP](https://github.com/pedrofran12/hpim_dm/tree/Test_IGMP) - Topology used to test our IGMPv2 implementation.
