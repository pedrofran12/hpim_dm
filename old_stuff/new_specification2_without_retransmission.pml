

/***********************NEW****************************************************/
#define N 4
#define NUMBER_OF_INTERFACES 10

#define BUFFER_SIZE 2
#define INFINITE_METRIC 255

#define i_win_assert(my_id, my_metric, other_id, other_metric) \
  (my_metric < other_metric || (my_metric== other_metric && my_id > other_id))
#define is_interested(state) (state == interest)

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

#define MSG_TYPE_TO_NEIGHBOR_STATE(msg_type) ((msg_type == msg_i_am_upstream) -> upstream : ((msg_type == msg_i_am_no_longer_upstream || msg_type == msg_interest) -> not_upstream_interest : not_upstream_interest))
#define NEIGHBORS_THAT_ACKED(node_id, interface_id) node_info[node_id].neighbors_that_acked_last_msg[interface_id]
#define DID_NEIGHBOR_ACKED(node_id, interface_id, neighbor_id) (NEIGHBORS_THAT_ACKED(node_id, interface_id) & (1 << interface_id)) != 0
#define NEIGHBORS_THAT_ACKED(node_id, interface_id) node_info[node_id].neighbors_that_acked_last_msg[interface_id]
#define ALL_NEIGHBORS_ACKED(node_id, interface_id) (NEIGHBORS_OF_INTERFACE(node_id, interface_id) == node_info[node_id].neighbors_that_acked_last_msg[interface_id])
#define LAST_TRANSMITTED_SN(node_id, interface_id) node_info[node_id].last_transmitted_sequence_number[interface_id]
#define LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) node_info[node_id].neighbor_state[interface_id].last_received_sn[neighbor_id]


#define ALL_MESSAGES_WERE_ACKED (LAST_TRANSMITTED_SN(0,1)==LAST_RECEIVED_SN(1,3,1) && LAST_TRANSMITTED_SN(1,3)==LAST_RECEIVED_SN(0,1,3) &&\
 LAST_TRANSMITTED_SN(0,2)==LAST_RECEIVED_SN(2,5,2) && LAST_TRANSMITTED_SN(2,5)==LAST_RECEIVED_SN(0,2,5) && \
 LAST_TRANSMITTED_SN(1,4)==LAST_RECEIVED_SN(3,7,4) && LAST_TRANSMITTED_SN(3,7)==LAST_RECEIVED_SN(1,4,7) && \
 LAST_TRANSMITTED_SN(2,6)==LAST_RECEIVED_SN(3,8,6) && LAST_TRANSMITTED_SN(3,8)==LAST_RECEIVED_SN(2,6,8))



mtype = {root, non_root, not_interface}; //interface can be of type Root or Non-Root
mtype = {active_tree, inactive_tree, unknown_tree}; // Tree can be in one of three states
mtype = {msg_i_am_upstream, msg_i_am_no_longer_upstream, msg_interest, msg_nointerest, msg_ack}; //type of messages
mtype = {upstream, not_upstream_interest, not_upstream_no_interest, not_neighbor}; //state of neighbors
mtype = {aw, al}; // assert state of non-root interfaces

typedef NEIGHBOR_STATE{
  mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  byte last_received_sn[NUMBER_OF_INTERFACES] = 0;
}

typedef NODE_CONFIGURATION {
	mtype tree_state = unknown_tree;
  mtype node_interface[NUMBER_OF_INTERFACES] = not_interface;
  bool luri = false;
  short luni = 0;
  short neighbors_at_each_interface[NUMBER_OF_INTERFACES] = 0;
  NEIGHBOR_STATE neighbor_state[NUMBER_OF_INTERFACES];
  byte last_transmitted_sequence_number[NUMBER_OF_INTERFACES] = 0;
  short neighbors_that_acked_last_msg[NUMBER_OF_INTERFACES] = 0;
}



//byte neighbor[NUMBER_OF_INTERFACES];
NODE_CONFIGURATION node_info[N];
chan ch[NUMBER_OF_INTERFACES] = [BUFFER_SIZE] of {mtype, byte, byte}; //<msg_type, neighbor_id, sn>;

inline recalculateTreeState(node_id, interface_id) {
	//d_step{
	bool found_upstream = false;
	short i;
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
      node_info[node_id].luni = (node_info[node_id].luni & (interface_id ^ 1023))
    :: else ->
      skip;
    fi;
    if
    :: !LURI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = active_tree
    :: LURI_IS_EMPTY(node_id) && !LUNI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = inactive_tree
    :: LURI_IS_EMPTY(node_id) && LUNI_IS_EMPTY(node_id) ->
      CURRENT_TREE_STATE(node_id) = unknown_tree
    fi;
	//}
}


inline sendMsg(node_id, msg_type, interface_id, sn) {
	//atomic{
	  short i;
		for (i : 0 .. NUMBER_OF_INTERFACES-1) {
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

inline sendMsgUnicast(node_id, msg_type, interface_id, sn, dst) {
	//atomic{
	if
  :: IS_NEIGHBOR(node_id, interface_id, dst) /*&& nfull(ch[dst])*/->
    printf("Interface %d is sending to %d\n", interface_id, dst)
    ch[dst] ! msg_type(interface_id, sn);
  :: !IS_NEIGHBOR(node_id, interface_id, dst) /*|| full(ch[dst])*/ ->
    printf("Interface %d is NOT sending to %d\n", interface_id, dst)
    skip;
  fi;
}


inline neighbor_acked(node_id, interface_id, neighbor_id) {
    node_info[node_id].neighbors_that_acked_last_msg[interface_id] = node_info[node_id].neighbors_that_acked_last_msg[interface_id] | (1 << neighbor_id)
}

/*
proctype Node(byte my_id) {
  do
  ::
  ::
  od;
}
*/
/*
proctype Interface(byte node_id, byte interface_id) {
  mtype neighbor_state[NUMBER_OF_INTERFACES] = none
  tree_state = unknown
  do
  :: nempty(ch[interface_id]) ->
    ch[interface_id] ? msg_type(neighbor_id, sn);
    if
    :: msg_type != msg_ack ->
      neighbor_state[neighbor_id] = MSG_TYPE_TO_NEIGHBOR_STATE(msg_type)
      recalculateTreeState(neighbor_state, interface_id, neighbor_state)
    :: else ->
      // processar msg ack
    fi
  :: INTERFACE_TYPE(my_id, interface_id) == root && (CURRENT_TREE_STATE(node_id) != tree_state || CURRENT_TREE_STATE(node_id) == unknown) ->

  :: INTERFACE_TYPE(my_id, interface_id) == non_root  && CURRENT_TREE_STATE(node_id) != tree_state ->
  od;
}
*/


//mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;


proctype InterfaceReceive(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype tree_state = unknown_tree;
  mtype msg_type;
  byte neighbor_id;
  byte sn;
  do
  :: nempty(ch[interface_id]) ->
  atomic {
    ch[interface_id] ?? msg_type(neighbor_id, sn);
    if
    :: msg_type != msg_ack && LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) < sn ->
      printf("%d interface id %d received non-ack message from %d\n", node_id, interface_id, neighbor_id);
      //printf("%e\n", msg_type);
      LAST_RECEIVED_SN(node_id, interface_id, neighbor_id) = sn;
      sendMsgUnicast(node_id, msg_ack, interface_id, sn, neighbor_id)
      NEIGHBOR_STATE(node_id, interface_id, neighbor_id) = MSG_TYPE_TO_NEIGHBOR_STATE(msg_type);
      //printf("Interface id %d with Neighbor id %d with state %e\n", interface_id, neighbor_id, MSG_TYPE_TO_NEIGHBOR_STATE(msg_type));

      recalculateTreeState(node_id, interface_id);
    :: msg_type == msg_ack && sn == LAST_TRANSMITTED_SN(node_id, interface_id) ->
      neighbor_acked(node_id, interface_id, neighbor_id);
    :: else ->
      printf("%d interface id %d received ack message from %d\n", node_id, interface_id, neighbor_id);
    fi;
    }
  od;
}


proctype InterfaceSend(byte node_id; byte interface_id) {
  //mtype neighbor_state[NUMBER_OF_INTERFACES] = not_neighbor;
  mtype last_interface_type = INTERFACE_TYPE(node_id, interface_id);
  mtype last_tree_state = unknown_tree;
  mtype last_msg_type = msg_i_am_no_longer_upstream
  mtype last_sn = 0

  // TODO VERIFICAR SE INTERFACE MUDA DE ROOT->NON-ROOT E NON-ROOT->ROOT
  do
  // interface do tipo root
  :: INTERFACE_TYPE(node_id, interface_id) == root && (CURRENT_TREE_STATE(node_id) != last_tree_state || last_interface_type == non_root) ->
    atomic {
      if
      :: last_interface_type == non_root && last_tree_state == active_tree ->
        last_interface_type = root;
        last_msg_type = msg_i_am_no_longer_upstream
        LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
        last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
        NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
        sendMsg(node_id, msg_i_am_no_longer_upstream, interface_id, last_sn);
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
      last_msg_type = msg_i_am_upstream
      LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_upstream, interface_id, last_sn);
    :: CURRENT_TREE_STATE(node_id)==active_tree && last_interface_type == root->
      last_interface_type = non_root;
      last_tree_state = active_tree;
      //send i am upstream
      last_msg_type = msg_i_am_upstream
      LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_upstream, interface_id, last_sn);
    :: last_tree_state == active_tree && (CURRENT_TREE_STATE(node_id) == inactive_tree || CURRENT_TREE_STATE(node_id) == unknown_tree) && last_interface_type == non_root ->
      printf("2 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
      //send i am no longer upstream
      last_msg_type = msg_i_am_upstream
      LAST_TRANSMITTED_SN(node_id, interface_id) = LAST_TRANSMITTED_SN(node_id, interface_id)+1
      last_sn = LAST_TRANSMITTED_SN(node_id, interface_id)
      NEIGHBORS_THAT_ACKED(node_id, interface_id) = 0;
      sendMsg(node_id, msg_i_am_no_longer_upstream, interface_id, last_sn)
    :: last_interface_type == root && (CURRENT_TREE_STATE(node_id) == inactive_tree || CURRENT_TREE_STATE(node_id) == unknown_tree) ->
      last_tree_state = CURRENT_TREE_STATE(node_id);
      last_interface_type = non_root;
    :: else ->
      printf("3 > Interface ID %d entrou\n", interface_id);
      last_tree_state = CURRENT_TREE_STATE(node_id);
    fi;
    }
/*  :: last_sn == LAST_TRANSMITTED_SN(node_id, interface_id) && !ALL_NEIGHBORS_ACKED(node_id, interface_id) ->
    atomic{
    sendMsg(node_id, last_msg_type, interface_id, last_sn)
  }*/
  od;
}

/*
proctype Unicast() {
  byte aw_metric;
  byte i, node_id;
	atomic {


		select(node_id : 0 .. 3);

    //select(aw_metric : 10 .. 12);

		aw_metric = 15;

		node_metric[node_id] = aw_metric;
		unicast[node_id] ! change_metric(aw_metric);

		aw_metric = 255;
		aw_id = 0
		for(i : 0 .. N-1){
			// select new assert winner id
			if
			:: i_win_assert(i, node_metric[i], aw_id, aw_metric) ->
				aw_id = i;
				aw_metric = node_metric[i];
			:: else ->
				skip;
			fi;
		}
		change_at_metric++;
	}

  atomic {
  node_id = 2;
  //select(aw_metric : 10 .. 12);
  aw_metric = 14;

  node_metric[node_id] = aw_metric;
  unicast[node_id] ! change_metric(aw_metric);

  aw_metric = 255;
  aw_id = 0
  for(i : 0 .. N-1){
    // select new assert winner id
    if
    :: i_win_assert(i, node_metric[i], aw_id, aw_metric) ->
      aw_id = i;
      aw_metric = node_metric[i];
    :: else ->
      skip;
    fi;
  }
  change_at_metric++;
}
}
*/


init {
  node_info[0].tree_state = active_tree
  node_info[0].luri = true
  node_info[0].node_interface[0] = root
  node_info[0].node_interface[1] = non_root
  node_info[0].node_interface[2] = non_root
  node_info[0].neighbors_at_each_interface[1] = 1 << 3
  node_info[0].neighbors_at_each_interface[2] = 1 << 5

  node_info[1].node_interface[3] = root
  node_info[1].node_interface[4] = non_root
  node_info[1].neighbors_at_each_interface[3] = 1 << 1
  node_info[1].neighbors_at_each_interface[4] = 1 << 7

  node_info[2].node_interface[5] = root
  node_info[2].node_interface[6] = non_root
  node_info[2].neighbors_at_each_interface[5] = 1 << 2
  node_info[2].neighbors_at_each_interface[6] = 1 << 8

  node_info[3].node_interface[7] = root
  node_info[3].node_interface[8] = non_root
  node_info[3].node_interface[9] = non_root
  node_info[3].neighbors_at_each_interface[7] = 1 << 4
  node_info[3].neighbors_at_each_interface[8] = 1 << 6
	//node_metric[0] = INFINITE_METRIC;
	//node_metric[1] = 9;
	//node_metric[2] = 16;
	//atomic{
    //run Node(0, nointerest, INFINITE_METRIC);
		//run Node(1, aw, 9);
		//run Node(2, aw, 16);
		//run Node(3, interest, INFINITE_METRIC);
	//}
	atomic{
    printf("FUCK\n")
    run InterfaceReceive(0, 0);
    run InterfaceSend(0, 0);

    run InterfaceReceive(0, 1);
    run InterfaceSend(0, 1);

    run InterfaceReceive(0, 2);
    run InterfaceSend(0, 2);

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

    run InterfaceReceive(3, 9);
    run InterfaceSend(3, 9);

    //run Unicast();
		//run Unicast(1, 15);
    //run Unicast(2, 14);
		//change_at_metric = true;
	}
}











/*
proctype Node(byte my_id; mtype starting_state; byte my_metric) {
	// All states
		byte last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
		byte metric_of_aw = INFINITE_METRIC;
		bool is_updated = false;
		byte new_metric;
		byte neighbor_id;
	// MSG info
		mtype msg_type;
		byte source;
		byte metric_rcv;
		ENTRY recv_entries;

		bool fail = false;
		bool i_have_better_metric = false;
		bool recv_fresher_state = false;
		bool quack_is_uptodate = false;

	initEntries(my_id, starting_state, global_entries[my_id]);
endsnode:
	do
  :: STATE_ME(my_id) == aw ->
    atomic {
		if
		:: nempty(ch[my_id]) && empty(unicast[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			recv_fresher_state = (global_entries[my_id].sequence_number[source] < recv_entries.sequence_number[source]);
			i_have_better_metric = i_win_assert(my_id, my_metric, source, metric_rcv);
			if
			:: msg_type == msg_quack ->
				if
				// recv worse metric
				:: i_have_better_metric ->
					// i am still aw
					if
					// compare sequence number to update entry
					:: recv_fresher_state ->
                SN_OF(my_id, source) = recv_entries.sequence_number[source];
                STATE_OF(my_id, source) = recv_entries.state[source];
						//checkUpdated(my_id, global_entries[my_id], is_updated);

					:: else -> skip;
					fi;
					checkUpdated(my_id, global_entries[my_id], is_updated);
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
				:: !i_have_better_metric ->
					// i am assert loser
					last_neighbor_quack = source;
					metric_of_aw = metric_rcv;
					is_updated = false;
          STATE_ME(my_id) = al;
          SN_ME(my_id)++;
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
				fi;
			:: msg_type == msg_nointerest || msg_type == msg_interest ->
				if
				:: i_have_better_metric ->
              if
              // compare sequence number to update entry
              :: recv_fresher_state ->
                SN_OF(my_id, source) = recv_entries.sequence_number[source];
                STATE_OF(my_id, source) = recv_entries.state[source];
                checkUpdatedOfNonQuackMsg(my_id, global_entries[my_id], recv_entries, is_updated);
                sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);

              :: !recv_fresher_state ->
                checkUpdatedOfNonQuackMsg(my_id, global_entries[my_id], recv_entries, is_updated);
                sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
              fi;

				:: !i_have_better_metric ->
						sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
				fi;


				//printEntries(my_id, global_entries[my_id]);
			fi;
		:: nempty(unicast[my_id]) ->
				unicast[my_id] ? msg_type(new_metric);
				if
				:: new_metric > my_metric ->
						is_updated = false;
						clearEntries(global_entries[my_id], my_id);
						sendMsg(msg_quack, my_id, new_metric, global_entries[my_id]);
				:: else ->
						skip;
				fi;
				my_metric = new_metric
		:: empty(ch[my_id]) && empty(unicast[my_id]) && !is_updated ->
			sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
		fi;
    }

	:: STATE_ME(my_id) == al ->
    atomic {
		if
		:: nempty(ch[my_id]) && empty(unicast[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			i_have_better_metric = i_win_assert(my_id, my_metric, source, metric_rcv);
			if
			:: msg_type == msg_quack ->
                quack_is_uptodate = SN_ME(my_id) == recv_entries.sequence_number[my_id]
				if
				// recv worse metric
				:: i_have_better_metric ->
					// i am aw
          STATE_ME(my_id) = aw;
          SN_ME(my_id)++;
					clearEntries(global_entries[my_id], my_id)
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
					last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
					metric_of_aw = INFINITE_METRIC;

				:: !i_have_better_metric && quack_is_uptodate ->
					last_neighbor_quack = source;
					metric_of_aw = metric_rcv;
					is_updated = true;

				:: !i_have_better_metric && !quack_is_uptodate ->
					//last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
					//metric_of_aw = INFINITE_METRIC;
					is_updated = false;
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);

        :: else -> skip;

				fi;

			:: msg_type == msg_interest || msg_type == msg_nointerest ->
				if
				:: source == last_neighbor_quack && i_have_better_metric ->
					STATE_ME(my_id) = aw;
          SN_ME(my_id)++;
					clearEntries(global_entries[my_id], my_id)
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
					last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
					metric_of_aw = INFINITE_METRIC;

				:: source == last_neighbor_quack && !i_have_better_metric ->
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
					//last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
					//metric_of_aw = INFINITE_METRIC;

				:: source != last_neighbor_quack -> skip;
				fi;
			fi;
		:: nempty(unicast[my_id]) ->
				unicast[my_id] ? msg_type(new_metric);
				if
				:: my_metric!=new_metric && i_win_assert(my_id, new_metric, last_neighbor_quack, metric_of_aw) ->
						global_entries[my_id].state[my_id] = aw;
						global_entries[my_id].sequence_number[my_id]++;
						clearEntries(global_entries[my_id], my_id);
						sendMsg(msg_quack, my_id, new_metric, global_entries[my_id]);
						is_updated = false;
						metric_of_aw = INFINITE_METRIC;
						last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
				:: my_metric!=new_metric && !i_win_assert(my_id, new_metric, last_neighbor_quack, metric_of_aw) ->
            is_updated = false;
            global_entries[my_id].sequence_number[my_id]++;
            sendMsg(msg_nointerest, my_id, new_metric, global_entries[my_id]);
        :: else ->
            skip;
				fi;
				my_metric = new_metric;
		:: empty(ch[my_id]) && empty(unicast[my_id]) && !is_updated ->
			sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
		fi;
    }

	:: STATE_ME(my_id) == nointerest || STATE_ME(my_id) == interest ->
    atomic {
		if
		:: nempty(ch[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			if
			:: msg_type == msg_quack ->
				quack_is_uptodate = SN_ME(my_id) == recv_entries.sequence_number[my_id]
				if
				:: quack_is_uptodate ->
					is_updated = true;
					last_neighbor_quack = source;
					metric_of_aw = metric_rcv;
				:: !quack_is_uptodate ->
					is_updated = false;
					msg_type = ((is_interested(STATE_ME(my_id))) -> msg_interest : msg_nointerest);
					sendMsg(msg_type, my_id, INFINITE_METRIC, global_entries[my_id]);
					last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
					metric_of_aw = INFINITE_METRIC;
				fi;
			:: else -> skip;
			fi;

		:: empty(ch[my_id]) /*&& empty(failure_detector_channel[my_id]) && !is_updated ->
          msg_type = ((is_interested(STATE_ME(my_id))) -> msg_interest : msg_nointerest);
          sendMsg(msg_type, my_id, INFINITE_METRIC, global_entries[my_id]);
		fi;
    }
	od;
}
*/
