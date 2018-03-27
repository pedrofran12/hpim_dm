#define N 3
#define BUFFER_SIZE 20
#define INFINITE_METRIC 255


mtype = {msg_interest, msg_nointerest, msg_quack};
mtype = {noinfo, interest, nointerest, aw, al};

typedef ENTRY {
	mtype state[N] = noinfo;
	byte sequence_number[N] = 0;
}

ENTRY global_entries[N];
#define test (global_entries[1].state[0] == nointerest && global_entries[1].state[1] == aw && global_entries[1].state[2] == al)
				//msgtype, source, metric, array_entries
chan ch[N] = [BUFFER_SIZE] of {mtype, byte, byte, ENTRY};

// set my initial state
inline initEntries(my_id, initial_state, entries) {
	entries.state[my_id] = initial_state;
	entries.sequence_number[my_id] = 1;
}

// send msg reliably
inline sendMsg(msg_type, me, metric, entries) {
	byte i;
	//int aux[N] = {0, 0, 0, 0};
	atomic{
		for (i : 0 .. N-1) {
			if
			// discard if my channel
			:: i == me -> skip;
			// randomly send if not my channel
			:: i != me ->
				ch[i] ! msg_type(me, metric, entries);
				//aux[i] = len(ch[i]);
			fi;
		}
	//printf("%d sent %e: %d %d %d %d\n", me, msg_type, aux[0], aux[1], aux[2], aux[3])
	}
}

// check if AssertWinner is updated
inline checkUpdated(my_id, entries, is_updated) {
	is_updated = true;
	byte i;
	atomic{
		for (i : 0 .. N-1) {
			if
			:: entries.sequence_number[i] == 0 || (entries.state[i] == aw && i!=my_id)->
				is_updated = false;
				break;
			:: else ->
				skip;
			fi;
		}
	}
}


inline checkUpdatedOfNonQuackMsg(entries, recv_entries, is_updated) {
	is_updated = true;
	byte i, j;
	atomic{
	for (i : 0 .. N-1) {
		if
		// if entry received has a higher valuer => aw should ask information about this node...
		// because that node already sent fresher info but wasnt received by aw
		:: recv_entries.sequence_number[i] > entries.sequence_number[j] ->
			entries.state[j] = noinfo;
			entries.sequence_number[j] = 0;
			is_updated = false; // node should send info
		:: recv_entries.sequence_number[i] == 0 && entries.sequence_number[j] == 0 ->
			is_updated = false;
		:: else ->
			skip;
		fi;
	}
	}
}

inline clearEntries(entries, my_id) {
	byte i;
	d_step{
		for (i : 0 .. N-1) {
			if
			:: i == my_id ->
				skip;
			:: else ->
				entries.sequence_number[i] = 0;
				entries.state[i] = noinfo;
			fi;
		}
	}
}

inline printEntries(my_id, entries) {
	byte i = 0;
	atomic {
		printf("i am process %d\n", my_id);
		for(i : 0 .. (N-1)) {
			printf("    %d   %e   %d\n", i, entries.state[i], entries.sequence_number[i]);
		}
	}
}


proctype Node(byte my_id; mtype starting_state; byte initial_metric) {
	// All states
		//ENTRY entries;
		byte last_neighbor_quack = 100; //nao usado
		byte my_metric = initial_metric;
		byte metric_of_aw = 0;
		bool is_updated = false;
	// MSG info
		mtype msg_type;
		byte source;
		byte metric_rcv;
		ENTRY recv_entries;

	bit i_have_better_metric = false;
	bit recv_fresher_state = false;
	bit quack_is_uptodate = false;

	initEntries(my_id, starting_state, global_entries[my_id]);

endsnode:
	do
	:: global_entries[my_id].state[my_id] == aw ->
		atomic {
		if
		:: nempty(ch[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			recv_fresher_state = (global_entries[my_id].sequence_number[source] < recv_entries.sequence_number[source]);
			if
			:: msg_type == msg_quack ->
				i_have_better_metric = my_metric < metric_rcv || (my_metric == metric_rcv && my_id > source);
				if
				// recv worse metric
				:: i_have_better_metric ->
					// i am still aw
					if
					// compare sequence number to update entry
					:: recv_fresher_state ->
						global_entries[my_id].sequence_number[source] = recv_entries.sequence_number[source];
						global_entries[my_id].state[source] = recv_entries.state[source];
						sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
						checkUpdated(my_id, global_entries[my_id], is_updated);
					:: else -> skip;
					fi;
				:: !i_have_better_metric ->
					// i am assert loser
					global_entries[my_id].state[my_id] = al;
					global_entries[my_id].sequence_number[my_id]++;
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
				fi;
			:: msg_type == msg_nointerest || msg_type == msg_interest ->
				if
				// compare sequence number to update entry
				:: recv_fresher_state ->
					global_entries[my_id].sequence_number[source] = recv_entries.sequence_number[source];
					global_entries[my_id].state[source] = recv_entries.state[source];
					checkUpdatedOfNonQuackMsg(global_entries[my_id], recv_entries, is_updated);
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
				:: !recv_fresher_state -> skip;
					checkUpdatedOfNonQuackMsg(global_entries[my_id], recv_entries, is_updated);
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
				fi;
				//checkUpdated(my_id, global_entries[my_id], is_updated);
				//printEntries(my_id, global_entries[my_id]);
			fi;
		:: empty(ch[my_id]) && !is_updated ->
			sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
		fi;
		}
	:: global_entries[my_id].state[my_id] == al ->
		atomic {
		if
		:: nempty(ch[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			i_have_better_metric = my_metric < metric_rcv || (my_metric == metric_rcv && my_id > source);
			if
			:: msg_type == msg_quack ->
				quack_is_uptodate = global_entries[my_id].sequence_number[source] == recv_entries.sequence_number[source]
				if
				// recv worse metric
				:: i_have_better_metric ->
					// i am aw
					global_entries[my_id].state[my_id] = aw;
					global_entries[my_id].sequence_number[my_id]++;
					clearEntries(global_entries[my_id], my_id)
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
				:: !i_have_better_metric && quack_is_uptodate ->
					is_updated = true;
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
				:: !i_have_better_metric && !quack_is_uptodate ->
					is_updated = false;
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
				fi;
			:: msg_type == msg_interest || msg_type == msg_nointerest ->
				if
				:: source == last_neighbor_quack && i_have_better_metric ->
					global_entries[my_id].state[my_id] = aw;
					global_entries[my_id].sequence_number[my_id]++;
					clearEntries(global_entries[my_id], my_id)
					sendMsg(msg_quack, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
				:: source == last_neighbor_quack && !i_have_better_metric ->
					sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
					is_updated = false;
				:: source != last_neighbor_quack -> skip;
				fi;
			:: else -> skip;
			fi;
		:: empty(ch[my_id]) && !is_updated ->
			sendMsg(msg_nointerest, my_id, my_metric, global_entries[my_id]);
		fi;
	}
	:: global_entries[my_id].state[my_id] == nointerest ->
		atomic {
		if
		:: nempty(ch[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			if
			:: msg_type == msg_quack ->
				quack_is_uptodate = global_entries[my_id].sequence_number[source] == recv_entries.sequence_number[source]
				if
				:: quack_is_uptodate ->
					is_updated = true;
				:: !quack_is_uptodate ->
					is_updated = false;
					sendMsg(msg_nointerest, my_id, INFINITE_METRIC, global_entries[my_id]);
				fi;
			:: else -> skip;
			fi;
		:: empty(ch[my_id]) && !is_updated ->
			sendMsg(msg_nointerest, my_id, INFINITE_METRIC, global_entries[my_id]);
		fi;
	}
	:: global_entries[my_id].state[my_id] == interest ->
		atomic {
		if
		:: nempty(ch[my_id]) ->
			ch[my_id] ? msg_type(source, metric_rcv, recv_entries);
			if
			:: msg_type == msg_quack ->
				quack_is_uptodate = global_entries[my_id].sequence_number[source] == recv_entries.sequence_number[source]
				if
				:: quack_is_uptodate ->
					is_updated = true;
				:: !quack_is_uptodate ->
					is_updated = false;
					sendMsg(msg_interest, my_id, INFINITE_METRIC, global_entries[my_id]);
				fi;
			:: else -> skip;
			fi;
		:: empty(ch[my_id]) && !is_updated ->
			sendMsg(msg_interest, my_id, INFINITE_METRIC, global_entries[my_id]);
		fi;
	}
	od;
}


init {
	run Node(0, nointerest, INFINITE_METRIC);
	run Node(1, aw, 10);
	run Node(2, aw, 20);
	//run Node(3, interest, INFINITE_METRIC);
}
