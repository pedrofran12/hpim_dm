#define N 5
#define NUMBER_OF_INTERFACES 10

#define BUFFER_SIZE 2
#define INFINITE_METRIC 255

#define INTERFACE_TYPE(node_id, interface_id) node_info[node_id].node_interface[interface_id]
#define IS_NEIGHBOR(node_id, interface_id, neighbor_id) ((NEIGHBORS_OF_INTERFACE(node_id, interface_id) & (1 << neighbor_id)) != 0)
#define NEIGHBORS_OF_INTERFACE(node_id, interface_id) node_info[node_id].neighbors_at_each_interface[interface_id]
#define NEIGHBOR_STATE(node_id, interface_id, neighbor_id) node_info[node_id].neighbor_state[interface_id].neighbor_state[neighbor_id]

#define CURRENT_TREE_STATE(my_id) node_info[my_id].tree_state
#define LURI_IS_EMPTY(my_id) node_info[my_id].luri == false
#define LUNI_IS_EMPTY(my_id) node_info[my_id].luni == 0

#define MY_RPC(my_id) node_info[my_id].my_rpc
#define NEIGHBOR_RPC(my_id, interface_id, neighbor_id) node_info[my_id].neighbor_state[interface_id].my_rpc[neighbor_id]


//#define MSG_TYPE_TO_NEIGHBOR_STATE(msg_type) ((msg_type == msg_i_am_upstream) -> upstream : ((msg_type == msg_i_am_no_longer_upstream || msg_type == msg_interest) -> not_upstream_interest : not_upstream_no_interest))
#define MSG_TYPE_TO_NEIGHBOR_STATE(msg_type) ((msg_type == msg_i_am_upstream) -> upstream : no_info)
#define NEIGHBORS_THAT_ACKED(node_id, interface_id) node_info[node_id].neighbors_that_acked_last_msg[interface_id]
#define DID_NEIGHBOR_ACKED(node_id, interface_id, neighbor_id) (NEIGHBORS_THAT_ACKED(node_id, interface_id) & (1 << interface_id)) != 0
#define NEIGHBORS_THAT_ACKED(node_id, interface_id) node_info[node_id].neighbors_that_acked_last_msg[interface_id]
#define ALL_NEIGHBORS_ACKED(node_id, interface_id) (NEIGHBORS_OF_INTERFACE(node_id, interface_id) == node_info[node_id].neighbors_that_acked_last_msg[interface_id])
#define LAST_TRANSMITTED_SN(node_id, interface_id) node_info[node_id].last_transmitted_sequence_number[interface_id]
#define LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) node_info[node_id].neighbor_state[interface_id].last_received_sn[neighbor_id]


mtype = {root, non_root, not_interface}; //interface can be of type Root or Non-Root
mtype = {active_tree, unsure_tree, inactive_tree}; // Tree can be in one of three states
mtype = {msg_i_am_upstream, msg_i_am_no_longer_upstream, msg_interest, msg_nointerest, msg_ack}; //type of messages
mtype = {upstream, not_upstream_interest, not_upstream_no_interest, no_info}; //state of neighbors
mtype = {aw, al}; // assert state of non-root interfaces

typedef NEIGHBOR_STATE{
  mtype neighbor_state[NUMBER_OF_INTERFACES] = no_info;
  byte my_rpc[NUMBER_OF_INTERFACES] = 255;
}

typedef NODE_CONFIGURATION {
	mtype tree_state = inactive_tree;
  mtype node_interface[NUMBER_OF_INTERFACES] = not_interface;
  bool luri = false;
  short luni = 0;
  byte my_rpc = 0;
  short neighbors_at_each_interface[NUMBER_OF_INTERFACES] = 0;
  NEIGHBOR_STATE neighbor_state[NUMBER_OF_INTERFACES];
}



//byte neighbor[NUMBER_OF_INTERFACES];
NODE_CONFIGURATION node_info[N];
chan ch[NUMBER_OF_INTERFACES] = [BUFFER_SIZE] of {mtype, byte, byte}; //<msg_type, neighbor_id, rpc>;

inline recalculateTreeState(node_id, interface_id) {
	//d_step{
  atomic {
	bool found_upstream = false;
	byte i;
		for (i : 0 .. NUMBER_OF_INTERFACES-1) {
			if
			:: NEIGHBOR_STATE(node_id, interface_id, i) == upstream && INTERFACE_TYPE(node_id, interface_id) == root ->
        if
        :: MY_RPC(node_id) > NEIGHBOR_RPC(node_id, interface_id, i) ->
            node_info[node_id].luri = true;
            found_upstream = true;
    				break;
        :: else ->
            skip;
        fi;
      :: NEIGHBOR_STATE(node_id, interface_id, i) == upstream && INTERFACE_TYPE(node_id, interface_id) == non_root ->
        node_info[node_id].luni = node_info[node_id].luni | (1 << interface_id);
				found_upstream = true;
        break;
      :: else ->
				skip;
			fi;
		}
    if
    :: !found_upstream && INTERFACE_TYPE(node_id, interface_id) == root ->
      node_info[node_id].luri = false
    :: !found_upstream && INTERFACE_TYPE(node_id, interface_id) == non_root ->
      node_info[node_id].luni = (node_info[node_id].luni & (32767 ^ (1 << interface_id)))
    :: else ->
      skip;
    fi;
    if
    :: !LURI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = active_tree;
    :: LURI_IS_EMPTY(node_id) && !LUNI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = unsure_tree;
    :: LURI_IS_EMPTY(node_id) && LUNI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = inactive_tree;
    fi;
    printf("CURRENT_STATE of node %d is %e\n\n\n", node_id, CURRENT_TREE_STATE(node_id))
  }
	//}
}


inline sendMsg(node_id, msg_type, interface_id, rpc) {
	  byte i;
    atomic{
		for (i : 0 .. (NUMBER_OF_INTERFACES-1)) {
      sendMsgUnicast(node_id, msg_type, interface_id, rpc, i);
		}
    }
}

inline sendMsgUnicast(node_id, msg_type, interface_id, rpc, dst) {
	atomic{
	if
  :: IS_NEIGHBOR(node_id, interface_id, dst) ->
    printf("Interface %d is sending to %d\n", interface_id, dst);
    ch[dst] ! msg_type(interface_id, rpc);
  :: !IS_NEIGHBOR(node_id, interface_id, dst) /*|| full(ch[dst])*/ ->
    printf("Interface %d is NOT sending to %d\n", interface_id, dst);
    skip;
  fi;
}
}


proctype InterfaceReceive(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype tree_state = inactive_tree;
  mtype msg_type;
  byte neighbor_id;
  byte neighbor_rpc;

//  atomic {
end:
  do
  :: nempty(ch[interface_id]) ->
  atomic {
    ch[interface_id] ? msg_type(neighbor_id, neighbor_rpc);
    if
    :: msg_type != msg_ack && IS_NEIGHBOR(node_id, interface_id, neighbor_id) ->
      printf("%d interface id %d received non-ack message from %d\n", node_id, interface_id, neighbor_id);
      //printf("%e\n", msg_type);
      //LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) = sn;
      //sendMsgUnicast(node_id, msg_ack, interface_id, sn, neighbor_id)
      if
      :: msg_type == msg_i_am_upstream ->
          NEIGHBOR_STATE(node_id, interface_id, neighbor_id) = upstream;
          NEIGHBOR_RPC(node_id, interface_id, neighbor_id) = neighbor_rpc;
      :: else ->
          NEIGHBOR_STATE(node_id, interface_id, neighbor_id) = no_info;
          NEIGHBOR_RPC(node_id, interface_id, neighbor_id) = 255;
      fi;
      recalculateTreeState(node_id, interface_id);
    :: else ->
      printf("%d interface id %d received something message from %d\n", node_id, interface_id, neighbor_id);
    fi;
    }
  od;//}
}


proctype InterfaceSend(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype last_interface_type = INTERFACE_TYPE(node_id, interface_id);
  mtype last_tree_state = inactive_tree;
  mtype last_msg_type = msg_i_am_no_longer_upstream
  mtype last_sn = 0;
  byte last_rpc = MY_RPC(node_id);


  atomic {
end:
  do
  // interface do tipo root
  :: INTERFACE_TYPE(node_id, interface_id) == root && (CURRENT_TREE_STATE(node_id) != last_tree_state || last_interface_type == non_root) ->
      if
      :: last_interface_type == root && last_tree_state != CURRENT_TREE_STATE(node_id) ->
        last_tree_state = CURRENT_TREE_STATE(node_id);
        // send interest
      :: last_interface_type == non_root && last_tree_state == active_tree ->
        last_interface_type = root;
        last_tree_state = CURRENT_TREE_STATE(node_id);

        sendMsg(node_id, msg_i_am_no_longer_upstream, interface_id, 0);
      :: else ->
        last_interface_type = root;
        skip;
      fi;
  // interface do tipo non-root
  :: INTERFACE_TYPE(node_id, interface_id) == non_root  && (CURRENT_TREE_STATE(node_id) != last_tree_state  || last_interface_type == root || last_rpc != MY_RPC(node_id)) ->
    printf("Interface ID %d entrou\n", interface_id);
    last_rpc = MY_RPC(node_id);
    if
    :: last_interface_type == non_root && CURRENT_TREE_STATE(node_id) == active_tree ->
      printf("1 > Interface ID %d entrou\n", interface_id);
      last_tree_state = active_tree;
      //send i am upstream
      //last_msg_type = msg_i_am_upstream
      //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_upstream, interface_id, MY_RPC(node_id));
    :: last_interface_type == non_root && last_tree_state == active_tree && CURRENT_TREE_STATE(node_id) != active_tree ->
      printf("2 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
      //send i am no longer upstream
      //last_msg_type = msg_i_am_upstream
      //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_no_longer_upstream, interface_id, 0);
    :: last_interface_type == root && CURRENT_TREE_STATE(node_id) == active_tree ->
      last_interface_type = non_root;
      sendMsg(node_id, msg_i_am_upstream, interface_id, MY_RPC(node_id));
    :: else ->
      printf("3 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
      last_interface_type = non_root;
    fi;
  od;
  }
}



inline unicastChange(node_id, interface_id1, interface_id2) {
  atomic {
    mtype interface_type1 = INTERFACE_TYPE(node_id, interface_id1)
    mtype interface_type2 = INTERFACE_TYPE(node_id, interface_id2)

    INTERFACE_TYPE(node_id, interface_id1) = interface_type2;
    INTERFACE_TYPE(node_id, interface_id2) = interface_type1;

    recalculateTreeState(node_id, interface_id1);
    recalculateTreeState(node_id, interface_id2);
  }
}



inline nodeFailure(node_id) {
  atomic {
    byte node_id_iterator = 0;
    byte interface_to_fail = 0;
    byte interface_of_neighbor = 0;
    for(interface_to_fail: 0 .. NUMBER_OF_INTERFACES-1) {
        if
        :: (INTERFACE_TYPE(node_id, interface_to_fail) == root || INTERFACE_TYPE(node_id, interface_to_fail) == non_root) ->
            INTERFACE_TYPE(node_id, interface_to_fail) = not_interface;
            for (node_id_iterator: 0 .. N-1){
                for (interface_of_neighbor: 0 .. NUMBER_OF_INTERFACES-1) {
                    if
                    :: IS_NEIGHBOR(node_id_iterator, interface_of_neighbor, interface_to_fail) ->
                        printf("node %d remove neighbor %d\n", node_id_iterator, interface_to_fail);
                        NEIGHBORS_OF_INTERFACE(node_id_iterator, interface_of_neighbor) = NEIGHBORS_OF_INTERFACE(node_id_iterator, interface_of_neighbor) & (32767 ^ (1 << interface_to_fail));
                        NEIGHBOR_STATE(node_id_iterator, interface_of_neighbor, interface_to_fail) = no_info;
                        recalculateTreeState(node_id_iterator, interface_of_neighbor);
                    :: else ->
                        printf("NOT node %d remove neighbor %d\n", node_id_iterator, interface_to_fail);
                        skip;
                    fi;
                }
            }
        :: else ->
            skip;
        fi;
    }
  }
}



init {
  node_info[0].luri = true
  node_info[0].node_interface[0] = root
  node_info[0].node_interface[1] = non_root
  node_info[0].node_interface[2] = non_root
  node_info[0].my_rpc = 0
  node_info[0].neighbors_at_each_interface[1] = 1 << 3
  node_info[0].neighbors_at_each_interface[2] = 1 << 5

  node_info[1].node_interface[3] = root
  node_info[1].node_interface[4] = non_root
  node_info[1].my_rpc = 10
  node_info[1].neighbors_at_each_interface[3] = 1 << 1
  node_info[1].neighbors_at_each_interface[4] = (1 << 7) | (1 << 6)

  node_info[2].node_interface[5] = root
  node_info[2].node_interface[6] = non_root
  node_info[2].my_rpc = 10
  node_info[2].neighbors_at_each_interface[5] = 1 << 2
  node_info[2].neighbors_at_each_interface[6] = (1 << 4) | (1 << 7)

  node_info[3].node_interface[7] = root
  node_info[3].node_interface[8] = non_root
  node_info[3].my_rpc = 20
  node_info[3].neighbors_at_each_interface[7] = (1 << 4) | (1 << 6)
  node_info[3].neighbors_at_each_interface[8] = 1 << 9

  node_info[4].node_interface[9] = root
  node_info[4].my_rpc = 30
  node_info[4].neighbors_at_each_interface[9] = 1 << 8

	atomic{
    run InterfaceReceive(0, 1);
    run InterfaceSend(0, 1);

    run InterfaceSend(0, 2);
    run InterfaceReceive(0, 2);

    run InterfaceReceive(1, 3);
    run InterfaceSend(1, 3);

    run InterfaceReceive(1, 4);
    run InterfaceSend(1, 4);

    run InterfaceReceive(2, 5);
    run InterfaceSend(2, 5);

    run InterfaceReceive(2, 6);
    run InterfaceSend(2, 6);

    run InterfaceReceive(3, 7);
    run InterfaceSend(3, 7);

    run InterfaceReceive(3, 8);
    run InterfaceSend(3, 8);

    run InterfaceReceive(4, 9);
    run InterfaceSend(4, 9);

    node_info[0].tree_state = active_tree
	}

  atomic {
    nodeFailure(2);
  }
}

ltl ltl_test {(<>([](CURRENT_TREE_STATE(0)==active_tree && CURRENT_TREE_STATE(1)==active_tree && CURRENT_TREE_STATE(3)==active_tree  && CURRENT_TREE_STATE(4)==active_tree)))}
