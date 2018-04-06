#define N 3
#define BUFFER_SIZE 2
#define INFINITE_METRIC 255
#define NO_LAST_NEIGHBOR_QUACK 255

#define i_win_assert(my_id, my_metric, other_id, other_metric) \
  (my_metric < other_metric || (my_metric== other_metric && my_id > other_id))
#define is_interested(state) (state == interest)

#define STATE_OF(my_id, other_id) global_entries[my_id].state[other_id]
#define STATE_ME(my_id) STATE_OF(my_id, my_id)
#define SN_OF(my_id, other_id) global_entries[my_id].sequence_number[other_id]
#define SN_ME(my_id) SN_OF(my_id, my_id)

mtype = {msg_interest, msg_nointerest, msg_quack};
mtype = {noinfo, interest, nointerest, aw, al, dead};
mtype = {change_metric};
mtype = {delete_node, reset_node};

typedef ENTRY {
	mtype state[N] = noinfo;
	byte sequence_number[N] = 0;
}

byte neighbor[N];
ENTRY global_entries[N];
#define test (global_entries[1].state[0] == nointerest \
              && global_entries[1].state[1] == aw \
              && global_entries[1].state[2] == al)
				//msgtype, source, metric, array_entries
chan ch[N] = [BUFFER_SIZE] of {mtype, byte, byte, ENTRY};
chan unicast[N] = [1] of {mtype, byte};
chan failure_detector_channel[N] = [1] of {mtype, byte};

// set my initial state
inline initEntries(my_id, initial_state, entries) {
		entries.state[my_id] = initial_state;
		entries.sequence_number[my_id] = 1;
}

// send msg reliably
inline sendMsg(msg_type, me, metric, entries) {
	//atomic{
	byte i;
	//int aux[N] = {0, 0, 0, 0};
		for (i : 0 .. N-1) {
			if
			// discard if my channel or channel is full or msg is already in the
			// channel (but receiver didnt access the message)
			:: i == me || full(ch[i]) || ch[i]??[msg_type, eval(me), eval(metric)] -> skip;
			// send if not my channel and channel not full and message not in channel
			:: i != me && nfull(ch[i]) && !(ch[i]??[msg_type, eval(me), eval(metric)]) ->
				ch[i] ! msg_type(me, metric, entries);
				//aux[i] = len(ch[i]);
			fi;
		}
	//printf("%d sent %e: %d %d %d %d\n", me, msg_type, aux[0], aux[1], aux[2], aux[3])
	//}
}

// check if AssertWinner is updated
inline checkUpdated(my_id, entries, is_updated) {
	//d_step{
	is_updated = true;
	byte i;
		for (i : 0 .. N-1) {
			if
			:: entries.sequence_number[i] == 0 || (entries.state[i] == aw && i!=my_id)->
				is_updated = false;
				break;
			:: else ->
				skip;
			fi;
		}
	//}
}


inline checkUpdatedOfNonQuackMsg(my_id, entries, recv_entries, is_updated) {
	//d_step{
	is_updated = true;
	byte i;
	for (i : 0 .. N-1) {
		if
		// if entry received has a higher valuer => aw should ask information about this node...
		// because that node already sent fresher info but wasnt received by aw
		:: i!=my_id && recv_entries.sequence_number[i] > entries.sequence_number[i] ->
			entries.state[i] = noinfo;
			entries.sequence_number[i] = 0;
			is_updated = false; // node should send info
		:: i!=my_id && !(recv_entries.sequence_number[i] > entries.sequence_number[i]) && (entries.sequence_number[i] == 0 || entries.state[i] == aw)->
			is_updated = false;
		:: else ->
			skip;
		fi;
	}
	//}
}

inline clearEntries(entries, my_id) {
	//d_step{
	byte i;
		for (i : 0 .. N-1) {
			if
			:: i == my_id ->
				skip;
			:: else ->
				entries.sequence_number[i] = 0;
				entries.state[i] = noinfo;
			fi;
		}
	//}
}

/*
inline printEntries(my_id, entries) {
	byte i = 0;
	atomic {
/
		printf("i am process %d\n", my_id);
		for(i : 0 .. (N-1)) {
			printf("    %d   %e   %d\n", i, entries.state[i], entries.sequence_number[i]);
		}
/
//printf("1 is aw %d  :  2 is aw %d\n", global_entries[1].state[1]==aw, global_entries[2].state[2]==aw);
	}
}
*/

proctype Node(byte my_id; mtype starting_state; byte my_metric) {
	// All states
		byte last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
		byte metric_of_aw = INFINITE_METRIC;
		bool is_updated = false;
		byte new_metric;
		byte neighbor_id;
	// MSG info
		mtype msg_type;
		mtype msg_type_send;
		byte source;
		byte metric_rcv;
		ENTRY recv_entries;

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
		:: nempty(failure_detector_channel[my_id]) ->
				failure_detector_channel[my_id] ? msg_type(neighbor_id);
				if
				:: msg_type == delete_node ->
					neighbor[my_id] = neighbor[my_id] ^ (1 << (neighbor_id-1));
					global_entries[my_id].sequence_number[neighbor_id] = 255;
					global_entries[my_id].state[neighbor_id] = dead;
					checkUpdated(my_id, global_entries[my_id], is_updated);
				:: msg_type == reset_node ->
					neighbor[my_id] = neighbor[my_id] | (1 << (neighbor_id-1));
					global_entries[my_id].sequence_number[neighbor_id] = 0;
					global_entries[my_id].state[neighbor_id] = noinfo;
					is_updated = false;
				fi;
		:: empty(ch[my_id]) && empty(unicast[my_id]) && empty(failure_detector_channel[my_id]) && !is_updated ->
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
				:: else ->
						skip;
				fi;
				my_metric = new_metric;
		:: nempty(failure_detector_channel[my_id]) ->
				failure_detector_channel[my_id] ? msg_type(neighbor_id);
				if
				:: neighbor_id==last_neighbor_quack ->
						global_entries[my_id].state[my_id] = aw;
						global_entries[my_id].sequence_number[my_id]++;
						clearEntries(global_entries[my_id], my_id);
						is_updated=false;
						metric_of_aw = INFINITE_METRIC;
						last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
				:: else -> skip;
				fi;
				if
				:: msg_type == delete_node ->
					neighbor[my_id] = neighbor[my_id] ^ (1 << (neighbor_id-1));
				:: msg_type == reset_node ->
					neighbor[my_id] = neighbor[my_id] | (1 << (neighbor_id-1));
				fi;
		:: empty(ch[my_id]) && empty(unicast[my_id]) && empty(failure_detector_channel[my_id]) && !is_updated ->
			sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
		fi;
        }

	:: STATE_ME(my_id) == nointerest || STATE_ME(my_id) == interest ->
        atomic {
		if
		:: nempty(ch[my_id]) && empty(failure_detector_channel[my_id]) ->
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
					msg_type_send = ((is_interested(STATE_ME(my_id))) -> msg_interest : msg_nointerest);
					sendMsg(msg_type_send, my_id, INFINITE_METRIC, global_entries[my_id]);
					last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
					metric_of_aw = INFINITE_METRIC;
				fi;
			:: else -> skip;
			fi;
		:: nempty(failure_detector_channel[my_id]) ->
				failure_detector_channel[my_id] ? msg_type(neighbor_id);
				if
				:: neighbor_id==last_neighbor_quack ->
						is_updated=false;
						metric_of_aw = INFINITE_METRIC;
						last_neighbor_quack = NO_LAST_NEIGHBOR_QUACK;
				:: else -> skip;
				fi;
				if
				:: msg_type == delete_node ->
					neighbor[my_id] = neighbor[my_id] ^ (1 << (neighbor_id-1));
				:: msg_type == reset_node ->
					neighbor[my_id] = neighbor[my_id] | (1 << (neighbor_id-1));
				fi;
		:: empty(ch[my_id]) && empty(failure_detector_channel[my_id]) && !is_updated ->
                msg_type_send = ((STATE_ME(my_id) == interest) -> msg_interest : msg_nointerest);
				sendMsg(msg_type_send, my_id, INFINITE_METRIC, global_entries[my_id]);
		fi;
        }
	od;
}

byte aw_id;
bool change_at_metric = false;
byte node_metric[N];
//ltl test_unicast {[](<>((global_entries[1].state[1]==al) && \
			(global_entries[2].state[2]==aw) && (global_entries[2].state[1]==al) && \
			(global_entries[2].state[0]==nointerest)))}
proctype Unicast() {
	atomic {
		byte aw_metric;
		byte i, node_id;


		//select(node_id : 1 .. 2);
		node_id = 2;
		//select(aw_metric : 10 .. 12);
		aw_metric = 5;
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
		change_at_metric = true
	}
}



// Failure detector
/*
#define is_neighbor(my_neighbors, neighbor_id) ((my_neighbors >> neighbor_id) & 0x01) )
bool change_at_failure_detector = false;

proctype FailureDetector() {
	atomic {
		byte i, node_id;
		select(node_id : 0 .. N-1);

		for(i : 0 .. N-1){
			failure_detector_channel[i] ! delete_node(node_id);
		}
		change_at_failure_detector = true
	}
}
*/




init {
	node_metric[0] = INFINITE_METRIC;
	node_metric[1] = 10;
	node_metric[2] = 11;
	atomic{
		run Node(0, nointerest, INFINITE_METRIC);
		run Node(1, aw, 10);
		run Node(2, aw, 11);
		//run Node(3, interest, INFINITE_METRIC);
	}
	atomic{
		run Unicast();
		//change_at_metric = true;
	}
}
