#define N 5
#define NUMBER_OF_INTERFACES 12

#define BUFFER_SIZE 2
//#define INFINITE_METRIC 255

//#define i_win_assert(my_id, my_metric, other_id, other_metric) \
//  (my_metric < other_metric || (my_metric== other_metric && my_id > other_id))
//#define is_interested(state) (state == interest)

/*#define STATE_OF(my_id, other_id) global_entries[my_id].state[other_id]
#define STATE_ME(my_id) STATE_OF(my_id, my_id)
#define SN_OF(my_id, other_id) global_entries[my_id].sequence_number[other_id]
#define SN_ME(my_id) SN_OF(my_id, my_id)
*/

#define INTERFACE_TYPE(node_id, interface_id) node_info[node_id].node_interface[interface_id]
#define IS_NEIGHBOR(node_id, interface_id, neighbor_id) ((NEIGHBORS_OF_INTERFACE(node_id, interface_id) & (1 << neighbor_id)) != 0)
#define NEIGHBORS_OF_INTERFACE(node_id, interface_id) node_info[node_id].neighbors_at_each_interface[interface_id]
#define NEIGHBOR_STATE(node_id, interface_id, neighbor_id) node_info[node_id].neighbor_state[interface_id].neighbor_state[neighbor_id]

#define CURRENT_TREE_STATE(my_id) node_info[my_id].tree_state
#define LURI_IS_EMPTY(my_id) node_info[my_id].luri == false
#define LUNI_IS_EMPTY(my_id) node_info[my_id].luni == 0

//#define MSG_TYPE_TO_NEIGHBOR_STATE(msg_type) ((msg_type == msg_i_am_upstream) -> upstream : ((msg_type == msg_i_am_no_longer_upstream || msg_type == msg_interest) -> not_upstream_interest : not_upstream_no_interest))
#define MSG_TYPE_TO_NEIGHBOR_STATE(msg_type) ((msg_type == msg_i_am_upstream) -> upstream : no_info)
#define NEIGHBORS_THAT_ACKED(node_id, interface_id) node_info[node_id].neighbors_that_acked_last_msg[interface_id]
#define DID_NEIGHBOR_ACKED(node_id, interface_id, neighbor_id) (NEIGHBORS_THAT_ACKED(node_id, interface_id) & (1 << interface_id)) != 0
#define NEIGHBORS_THAT_ACKED(node_id, interface_id) node_info[node_id].neighbors_that_acked_last_msg[interface_id]
#define ALL_NEIGHBORS_ACKED(node_id, interface_id) (NEIGHBORS_OF_INTERFACE(node_id, interface_id) == node_info[node_id].neighbors_that_acked_last_msg[interface_id])
#define LAST_TRANSMITTED_SN(node_id, interface_id) node_info[node_id].last_transmitted_sequence_number[interface_id]
#define LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) node_info[node_id].neighbor_state[interface_id].last_received_sn[neighbor_id]


#define ALL_MESSAGES_WERE_ACKED (LAST_TRANSMITTED_SN(0,1)==LAST_RECEIVED_SN(1,3,1) && LAST_TRANSMITTED_SN(1,3)==LAST_RECEIVED_SN(0,1,3) &&\
 LAST_TRANSMITTED_SN(0,2)==LAST_RECEIVED_SN(2,5,2) && LAST_TRANSMITTED_SN(2,5)==LAST_RECEIVED_SN(0,2,5) && \
 LAST_TRANSMITTED_SN(1,4)==LAST_RECEIVED_SN(2,6,4) && LAST_TRANSMITTED_SN(1,4)==LAST_RECEIVED_SN(3,7,4) && \
 LAST_TRANSMITTED_SN(2,6)==LAST_RECEIVED_SN(1,4,6) && LAST_TRANSMITTED_SN(2,6)==LAST_RECEIVED_SN(3,7,6) && \
 LAST_TRANSMITTED_SN(3,7)==LAST_RECEIVED_SN(1,4,7) && LAST_TRANSMITTED_SN(3,7)==LAST_RECEIVED_SN(2,6,7) && \
 LAST_TRANSMITTED_SN(3,8)==LAST_RECEIVED_SN(4,9,8) && LAST_TRANSMITTED_SN(4,9)==LAST_RECEIVED_SN(3,8,9))

#define TEST ((CURRENT_TREE_STATE(0)==active_tree) && (CURRENT_TREE_STATE(1)==active_tree) && (CURRENT_TREE_STATE(2)==active_tree) && (CURRENT_TREE_STATE(3)==active_tree) && (CURRENT_TREE_STATE(4)==active_tree))

mtype = {root, non_root, not_interface}; //interface can be of type Root or Non-Root
mtype = {active_tree, inactive_tree, unknown_tree}; // Tree can be in one of three states
mtype = {msg_i_am_upstream, msg_i_am_no_longer_upstream, msg_interest, msg_nointerest, msg_ack}; //type of messages
mtype = {upstream, not_upstream_interest, not_upstream_no_interest, no_info}; //state of neighbors
mtype = {aw, al}; // assert state of non-root interfaces

typedef NEIGHBOR_STATE{
  mtype neighbor_state[NUMBER_OF_INTERFACES] = no_info;
  //byte last_received_sn[NUMBER_OF_INTERFACES] = 0;
}

typedef NODE_CONFIGURATION {
	mtype tree_state = unknown_tree;
  mtype node_interface[NUMBER_OF_INTERFACES] = not_interface;
  bool luri = false;
  short luni = 0;
  short neighbors_at_each_interface[NUMBER_OF_INTERFACES] = 0;
  NEIGHBOR_STATE neighbor_state[NUMBER_OF_INTERFACES];
  //byte last_transmitted_sequence_number[NUMBER_OF_INTERFACES] = 0;
  //short neighbors_that_acked_last_msg[NUMBER_OF_INTERFACES] = 0;
}



//byte neighbor[NUMBER_OF_INTERFACES];
NODE_CONFIGURATION node_info[N];
chan ch[NUMBER_OF_INTERFACES] = [BUFFER_SIZE] of {mtype, byte, byte}; //<msg_type, neighbor_id, sn>;

inline recalculateTreeState(node_id, interface_id) {
	//d_step{
  atomic {
	bool found_upstream = false;
	byte i;
		for (i : 0 .. NUMBER_OF_INTERFACES-1) {
			if
			:: NEIGHBOR_STATE(node_id, interface_id, i) == upstream && INTERFACE_TYPE(node_id, interface_id) == root ->
        node_info[node_id].luri = true;
        found_upstream = true;
				break;
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
      CURRENT_TREE_STATE(node_id) = inactive_tree;
    :: LURI_IS_EMPTY(node_id) && LUNI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = unknown_tree;
    fi;
    printf("CURRENT_STATE of node %d is %e\n\n\n", node_id, CURRENT_TREE_STATE(node_id))
  }
	//}
}


inline sendMsg(node_id, msg_type, interface_id, sn) {
	//atomic{
	  byte i;
    atomic{
		for (i : 0 .. (NUMBER_OF_INTERFACES-1)) {
      sendMsgUnicast(node_id, msg_type, interface_id, sn, i);

			//if
      //:: IS_NEIGHBOR(node_id, interface_id, i) /*&& nfull(ch[i]) && !DID_NEIGHBOR_ACKED(node_id, interface_id, i)*/->
      //  printf("Interface %d is sending to %d\n", interface_id, i)
      //  ch[i] ! msg_type(interface_id, sn);
      //:: !IS_NEIGHBOR(node_id, interface_id, i) /*|| full(ch[i]) || DID_NEIGHBOR_ACKED(node_id, interface_id, i)*/->
      //  printf("Interface %d is NOT sending to %d\n", interface_id, i)
      //  skip;
      //fi;
		}
    }
}

inline sendMsgUnicast(node_id, msg_type, interface_id, sn, dst) {
	atomic{
	if
  :: IS_NEIGHBOR(node_id, interface_id, dst) ->
    printf("Interface %d is sending to %d\n", interface_id, dst);
    ch[dst] ! msg_type(interface_id, sn);
  :: !IS_NEIGHBOR(node_id, interface_id, dst) /*|| full(ch[dst])*/ ->
    printf("Interface %d is NOT sending to %d\n", interface_id, dst);
    skip;
  fi;
}
}


inline neighbor_acked(node_id, interface_id, neighbor_id) {
    node_info[node_id].neighbors_that_acked_last_msg[interface_id] = node_info[node_id].neighbors_that_acked_last_msg[interface_id] | (1 << neighbor_id)
}



//mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;


proctype InterfaceReceive(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype tree_state = unknown_tree;
  mtype msg_type;
  byte neighbor_id;
  byte sn;

//  atomic {
end:
  do
  :: nempty(ch[interface_id]) ->
  atomic {
    ch[interface_id] ? msg_type(neighbor_id, sn);
    if
    :: msg_type != msg_ack && IS_NEIGHBOR(node_id, interface_id, neighbor_id) ->
      printf("%d interface id %d received non-ack message from %d\n", node_id, interface_id, neighbor_id);
      //printf("%e\n", msg_type);
      //LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) = sn;
      //sendMsgUnicast(node_id, msg_ack, interface_id, sn, neighbor_id)
      if
      :: msg_type == msg_i_am_upstream ->
          NEIGHBOR_STATE(node_id, interface_id, neighbor_id) = upstream;
      :: else ->
          NEIGHBOR_STATE(node_id, interface_id, neighbor_id) = no_info;
      fi;
          //MSG_TYPE_TO_NEIGHBOR_STATE(msg_type);
      //printf("Interface id %d with Neighbor id %d with state %e\n", interface_id, neighbor_id, MSG_TYPE_TO_NEIGHBOR_STATE(msg_type));

      recalculateTreeState(node_id, interface_id);
    //:: msg_type == msg_ack ->//&& sn == LAST_TRANSMITTED_SN(node_id, interface_id) ->
      //neighbor_acked(node_id, interface_id, neighbor_id);
      //skip;
    :: else ->
      printf("%d interface id %d received something message from %d\n", node_id, interface_id, neighbor_id);
    fi;
    }
  od;//}
}

/*
proctype InterfaceSend(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype last_interface_type = INTERFACE_TYPE(node_id, interface_id);
  mtype last_tree_state = unknown_tree;
  mtype last_msg_type = msg_i_am_no_longer_upstream
  mtype last_sn = 0

  ends:do
  // interface do tipo root
  :: INTERFACE_TYPE(node_id, interface_id) == root && (CURRENT_TREE_STATE(node_id) != last_tree_state || last_interface_type == non_root) ->
    atomic {
      if
      :: last_interface_type == non_root && last_tree_state == active_tree ->
        last_interface_type = root;
        //last_msg_type = msg_i_am_no_longer_upstream;
        //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1;
        //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id);
        //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
        sendMsg(node_id, msg_i_am_no_longer_upstream, interface_id, 0);
      :: last_interface_type == non_root && last_tree_state != active_tree ->
        last_interface_type = root;
      :: else ->
        skip;
      fi;
      if
      :: last_tree_state != CURRENT_TREE_STATE(node_id) ->
        last_tree_state = CURRENT_TREE_STATE(node_id);
        // send interest
      :: else ->
        skip;
      fi;
    }
  // interface do tipo non-root
  :: INTERFACE_TYPE(node_id, interface_id) == non_root  && (CURRENT_TREE_STATE(node_id) != last_tree_state || last_interface_type == root) ->
    atomic {
    printf("Interface ID %d entrou\n", interface_id);
    if
    :: CURRENT_TREE_STATE(node_id) == active_tree && last_interface_type == non_root ->
      printf("1 > Interface ID %d entrou\n", interface_id);
      last_tree_state = active_tree;
      //send i am upstream
      //last_msg_type = msg_i_am_upstream
      //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_upstream, interface_id, 0);
    :: CURRENT_TREE_STATE(node_id)==active_tree && last_interface_type == root->
      last_interface_type = non_root;
      last_tree_state = active_tree;
      //send i am upstream
      //last_msg_type = msg_i_am_upstream
      //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_upstream, interface_id, 0);
    :: last_tree_state == active_tree && CURRENT_TREE_STATE(node_id) != active_tree && last_interface_type == non_root ->
      printf("2 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
      //send i am no longer upstream
      //last_msg_type = msg_i_am_upstream
      //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_no_longer_upstream, interface_id, 0)
    :: CURRENT_TREE_STATE(node_id) != active_tree && last_interface_type == root ->
      last_tree_state = CURRENT_TREE_STATE(node_id);
      last_interface_type = non_root;
    :: else ->
      printf("3 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
    fi;
    }
  od;
}*/

proctype InterfaceSend(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype last_interface_type = INTERFACE_TYPE(node_id, interface_id);
  mtype last_tree_state = unknown_tree;
  mtype last_msg_type = msg_i_am_no_longer_upstream
  mtype last_sn = 0


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
  :: INTERFACE_TYPE(node_id, interface_id) == non_root  && (CURRENT_TREE_STATE(node_id) != last_tree_state  || last_interface_type == root) ->
    printf("Interface ID %d entrou\n", interface_id);
    if
    :: last_interface_type == non_root && CURRENT_TREE_STATE(node_id) == active_tree ->
      printf("1 > Interface ID %d entrou\n", interface_id);
      last_tree_state = active_tree;
      //send i am upstream
      //last_msg_type = msg_i_am_upstream
      //LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      //last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      //NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_upstream, interface_id, 0);
    :: last_interface_type == non_root && last_tree_state == active_tree ->
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
      sendMsg(node_id, msg_i_am_upstream, interface_id, 0);
    :: else ->
      printf("3 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
      last_interface_type = non_root;
    fi;
/*  :: last_sn == LAST_TRANSMITTED_SN(node_id, interface_id) && !ALL_NEIGHBORS_ACKED(node_id, interface_id) ->
    atomic{
    sendMsg(node_id, last_msg_type, interface_id, last_sn)
  }*/
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
  node_info[0].neighbors_at_each_interface[1] = 1 << 3
  node_info[0].neighbors_at_each_interface[2] = 1 << 5

  node_info[1].node_interface[3] = root
  node_info[1].node_interface[4] = non_root
  node_info[1].node_interface[10] = non_root
  node_info[1].neighbors_at_each_interface[3] = 1 << 1
  node_info[1].neighbors_at_each_interface[4] = (1 << 7) | (1 << 6)
  node_info[1].neighbors_at_each_interface[10] = 1 << 11

  node_info[2].node_interface[5] = root
  node_info[2].node_interface[6] = non_root
  node_info[2].neighbors_at_each_interface[5] = 1 << 2
  node_info[2].neighbors_at_each_interface[6] = (1 << 4) | (1 << 7)

  node_info[3].node_interface[7] = root
  node_info[3].node_interface[8] = non_root
  node_info[3].neighbors_at_each_interface[7] = (1 << 4) | (1 << 6)
  node_info[3].neighbors_at_each_interface[8] = 1 << 9

  node_info[4].node_interface[9] = root
  node_info[4].node_interface[11] = non_root
  node_info[4].neighbors_at_each_interface[9] = 1 << 8
  node_info[4].neighbors_at_each_interface[11] = 1 << 10

	atomic{
    run InterfaceReceive(0, 1);
    run InterfaceSend(0, 1);

    run InterfaceSend(0, 2);
    run InterfaceReceive(0, 2);

    run InterfaceReceive(1, 3);
    run InterfaceSend(1, 3);

    run InterfaceReceive(1, 4);
    run InterfaceSend(1, 4);

    run InterfaceReceive(1, 10);
    run InterfaceSend(1, 10);

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

    run InterfaceReceive(4, 11);
    run InterfaceSend(4, 11);

    node_info[0].tree_state = active_tree
	}

  atomic {
    nodeFailure(3);
    unicastChange(4, 9, 11);
  }
}

ltl ltl_test {(<>([](CURRENT_TREE_STATE(0)==active_tree && CURRENT_TREE_STATE(1)==active_tree && CURRENT_TREE_STATE(2)==active_tree  && CURRENT_TREE_STATE(4)==active_tree)))}
