# Promela

#### Promela Topologies:
| ![Topology1](topology.png "Topology 1") | ![Topology2](topology1.png "Topology 2") |
|:---:|:---:|
| Topology 1 | Topology 2 |


#### How to perform tests:

`spin -a FILE_NAME.pml`

`gcc -O2 -o pan pan.c -DCOLLAPSE -DVECTORSZ=1500`

`./pan -a`


#### Tests:

 1. File new_specification_all_active.pml : initially all routers consider the tree to be in Unknown state, except the Originator router, which will trigger the creation of the tree. (topology1)
 2. File new_specification_node_1_fail.pml : same as the first test, except that concurrently, node 1 fails. Due to redundant paths, all nodes should still consider the tree to be Active. (topology1)
 3. File new_specification_node_2_fail.pml : same as above, but node 2 fails, intead of node 1. (topology1)
 4. File new_specification_node_3_fail.pml : same as the first test, but node 3 fails, concurrently to the creation of the tree. Nodes 0, 1 and 2 should still consider the tree to be Active, while node 4 should consider the tree to be Unknown (no redundant paths). (topology1)
 5. File new_specification_node_3_fail_with_redundant_path.pml : same as above, but due to redundant paths, the unicast routing protocol would detect the redundant path, causing a change of Root<->Non-Root interfaces of node 4. (topology2)



#### Promela strucutre:
Each node has the following information:
```
typedef NEIGHBOR_STATE{
  mtype neighbor_state[NUMBER_OF_INTERFACES] = no_info;
}

typedef NODE_CONFIGURATION {
	mtype tree_state = unknown_tree;
	mtype node_interface[NUMBER_OF_INTERFACES] = not_interface;
	bool luri = false;
	short luni = 0;
	short neighbors_at_each_interface[NUMBER_OF_INTERFACES] = 0;
	NEIGHBOR_STATE neighbor_state[NUMBER_OF_INTERFACES];
}
```

`tree_state` represents the state of the tree, being initially in state Unknown.

`node_interface` represents all possible interfaces. An interface can be in one of three state: root, non_root or not_interface. The first two represent an interface that belongs to this node, while the other state, means that the interface does not belong to this node. According to Figure Topology, Node 0 would have interface 0 as root, interface 1 and 2 as non_root and the remaining interfaces as not_interface.

`luri` is a boolean that controls if the root interface has upstream routers connected to it. This is used for recalculating the tree state whenever an upstream neighbor is added or removed.

`luni` is the same as `luri` but controls which non_root interfaces have upstream neighbors. This is represented as a short, because it is modeled in a binary format (if interface 1 is the only non_root interface that connects to upstream neighors, `luni` would be set to 2 (00000010) - this is just used to save resources).

`neighbors_at_each_interface` is an array of shorts, that represents which neighbors are connected to each interface. A neighbor corresponds to the interface(s) that an interface is connected to. Regarding node 0, all indexes would be set to 0, except index 1 that is connected to interface 3 (would be set to 8 - 00001000) and index 2 that is connected to interface 5 (would be set to 16 - 00010000).

`neighbor_state` same as above, but used to set the state of each neighbor, connected to each interface of a node (set to upstream, not upstream or no_info).



Each interface is modeled by two proctypes, one for the reception of packets (proctype InterfaceReceive) and the other for the transmission of packets (proctype InterfaceSend). For node 2, of Figure Topology 1, it would be associated with two proctype InterfaceSend and two proctype InterfaceReceive (for interface 5 and 6). 

The proctype InterfaceReceive receives control packets from a channel, manipulates the state of a neighbor and recalculates the tree state of a node.

The proctype InterfaceSend checks if the previous tree state is the same as the new state. If not, the interface transmits a message to its neighbors (IamUpstream or IamNoLongerUpstream).


A node can have multiple interfaces (multiple proctypes InterfaceSend and InterfaceReceive),  having each one the identifier of the node that it belongs. A reception of a control packets that manipulates the state of a neighbor, can change the state of the tree of all proctype InterfaceSend belonging to the same node.


If we want to test the failure of a node, all routers connected to the failed node will stop considering it as a neighbor (remove information from `neighbors_at_each_interface` and `neighbor_state`). This removal of information causes a recalculation of the tree state, in order to determine if there are still other upstream neighbors connected to a node.

If we want to test a change in the unicast routing protocol, we need to select two interfaces of the same node that will change roles. For example, if node 1 initially considers interface 3 as Root and interface 4 as Non-Root, we could test what would happen when interface 3 and 4 changes roles (interface 3 is now Non-Root and interface 4 is now Root). When this change happens, it is required to recalculate the tree state, since the new Root and Non-Root can change the state of the `luni` and `luri`.

