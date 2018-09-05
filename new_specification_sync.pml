#define N 2
#define BUFFER_SIZE 6


mtype = {sync, hello}; //types of messages
mtype = {unknown, master, slave, updated}; //Neighbor state
mtype = {reboot, broken_bidirectional_relationship}; //inform neighbor about a reboot


chan ch[N] = [BUFFER_SIZE] of {mtype, byte, byte, byte, byte, byte, byte, bool, bool}; //<neighbor_id, my_boot_time, neighbor_boot_time, my_snapshot_sn, neighbor_snapshot_sn, sync_sn, master_bit, more_bit>;
chan fail_ch[N] = [BUFFER_SIZE] of {mtype}; //<failure_type>;

mtype neighbor_state[N] = unknown; // state of neighbor of node i
byte TOTAL_MSGS_SYNC = 0; // Total number of Sync messages exchanged to verify if both nodes finished the SYnc process with the same CurrentSyncSN
byte current_sync_sn[N] = 0; // CurrentSyncSN of each node to verify if both nodes finished the sync process with the same CurrentSyncSN
byte my_boot_time[N] = 0; // boot time of own node to verify synchronization mechanism
byte neighbor_boot_time[N] = 0; // boot time of neighbor to verify synchronization mechanism
byte my_snapshot_sn[N] = 0; //my snapshot sn of own node to verify synchronization mechanism
byte neighbor_snapshot_sn[N] = 0; // neighbor snapshot sn of neighbor to verify synchronization mechanism


#define MASTER_FLAG(state_of_neighbor) (state_of_neighbor==slave) // message should have Master flag set or unset
#define MORE_FLAG(total_of_sync_msgs, current_sync_sn) (current_sync_sn <= total_of_sync_msgs) // flag More should be set or unset in Sync message


inline recv_sync_and_neighbor_is_master(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit) {
      bool process_this_message2 = true;
      if
      :: rcv_neighbor_boot_time > neighbor_boot_time[node_id] ->
          // received greater BootTime... means that neighbor rebooted during sync... need to restart synchronization and store new SNs from neighbor
          new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
          process_this_message2 = false;
      :: rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn > neighbor_snapshot_sn[node_id] ->
          // received same BootTime but greater SnapshotSN... means that neighbor wants to restart sync... need to restart synchronization and store new SN from neighbor
          new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
          process_this_message2 = false;
      :: rcv_neighbor_boot_time < neighbor_boot_time[node_id] || (rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn < neighbor_snapshot_sn[node_id]) ->
          // if receive lower BootTime or same BootTime but with a lower SnapshotSN means that I have received a message from a previous sync process... must ignore this message
          process_this_message2 = false;
      :: else ->
          // if same BootTime and SnapshotSN continue processing message
          skip;
      fi;

      if
      :: process_this_message2 && rcv_master_bit && rcv_sync_sn == current_sync_sn[node_id] && (rcv_sync_sn > 0 && rcv_my_snapshot_sn == my_snapshot_sn[node_id] || rcv_sync_sn == 0) ->
          ch[neighbor_id] ! sync(node_id, my_boot_time[node_id], neighbor_boot_time[node_id], my_snapshot_sn[node_id], neighbor_snapshot_sn[node_id], current_sync_sn[node_id], MASTER_FLAG(neighbor_state[node_id]), MORE_FLAG(total_of_sync_msgs, current_sync_sn[node_id]));
          if
          :: rcv_sync_sn > 0 && !MORE_FLAG(total_of_sync_msgs, current_sync_sn[node_id]) && !rcv_more_bit ->
              neighbor_state[node_id] = updated;
          :: else ->
              current_sync_sn[node_id] = current_sync_sn[node_id] + 1;
          fi;
      :: else ->
          printf("ELSE RCV_SYNC_AND_MASTER\n");
          skip;
      fi;
}


inline recv_sync_and_neighbor_is_slave(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit) {
      bool process_this_message1 = true;
      if
      :: rcv_neighbor_boot_time > neighbor_boot_time[node_id] ->
          // received greater BootTime... means that neighbor rebooted during sync... need to restart synchronization and store new SNs from neighbor
          new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
      :: rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn > neighbor_snapshot_sn[node_id] && current_sync_sn[node_id] == 0 ->
          // received same BootTime but greater SnapshotSN... means that neighbor wants to restart sync... if current SyncSN is 0 store new SN of neighbor and process this message
          neighbor_snapshot_sn[node_id] = rcv_neighbor_snapshot_sn;
      :: rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn > neighbor_snapshot_sn[node_id] && current_sync_sn[node_id] > 0 ->
          // received same BootTime but greater SnapshotSN... means that neighbor wants to restart sync... if current SyncSN is greater than 0 store all SNs and increment my SnapshotSN
          new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
      :: rcv_neighbor_boot_time < neighbor_boot_time[node_id] || (rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn < neighbor_snapshot_sn[node_id]) ->
          // if receive lower BootTime or same BootTime but with a lower SnapshotSN means that I have received a message from a previous sync process... must ignore this message
          process_this_message1 = false;
      :: else ->
          // if same BootTime and SnapshotSN continue processing message
          skip;
      fi;


      if
      :: process_this_message1 && rcv_sync_sn == current_sync_sn[node_id] && rcv_master_bit && rcv_sync_sn == 0 ->
          if
          :: node_id < neighbor_id ->
              current_sync_sn[node_id] = 0;
              neighbor_state[node_id] = master;
              recv_sync_and_neighbor_is_master(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
          :: else ->
              ch[neighbor_id] ! sync(node_id, my_boot_time[node_id], neighbor_boot_time[node_id], my_snapshot_sn[node_id], neighbor_snapshot_sn[node_id], current_sync_sn[node_id], MASTER_FLAG(neighbor_state[node_id]), MORE_FLAG(total_of_sync_msgs, current_sync_sn[node_id]));
          fi;
      :: process_this_message1 && rcv_sync_sn == current_sync_sn[node_id] && !rcv_master_bit && my_snapshot_sn[node_id] == rcv_my_snapshot_sn ->
          if
          :: current_sync_sn[node_id] > 0 && !MORE_FLAG(total_of_sync_msgs, current_sync_sn[node_id]) && !rcv_more_bit ->
              neighbor_state[node_id] = updated;
          :: else ->
              current_sync_sn[node_id] = current_sync_sn[node_id] + 1;
              ch[neighbor_id] ! sync(node_id, my_boot_time[node_id], neighbor_boot_time[node_id], my_snapshot_sn[node_id], neighbor_snapshot_sn[node_id], current_sync_sn[node_id], MASTER_FLAG(neighbor_state[node_id]), MORE_FLAG(total_of_sync_msgs, current_sync_sn[node_id]));
          fi;
      :: else ->
          printf("ELSE RCV_SYNC_AND_SLAVE\n");
          skip;
      fi;
}

inline recv_sync_and_neighbor_is_unknown(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit) {
    if
    :: rcv_sync_sn == 0 && rcv_master_bit ->
      neighbor_boot_time[node_id] = rcv_neighbor_boot_time;
      neighbor_snapshot_sn[node_id] = rcv_neighbor_snapshot_sn;
      neighbor_state[node_id] = master;
      my_snapshot_sn[node_id] = my_snapshot_sn[node_id] + 1;
      current_sync_sn[node_id] = 0;
      recv_sync_and_neighbor_is_master(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
    :: else ->
      new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
    fi;
}



inline new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit) {
      neighbor_state[node_id] = slave;
      neighbor_boot_time[node_id] = rcv_neighbor_boot_time;
      neighbor_snapshot_sn[node_id] = rcv_neighbor_snapshot_sn;
      my_snapshot_sn[node_id] = my_snapshot_sn[node_id] + 1;
      current_sync_sn[node_id] = 0;
      ch[neighbor_id] ! sync(node_id, my_boot_time[node_id], neighbor_boot_time[node_id], my_snapshot_sn[node_id], neighbor_snapshot_sn[node_id], current_sync_sn[node_id], MASTER_FLAG(neighbor_state[node_id]), MORE_FLAG(total_of_sync_msgs, current_sync_sn[node_id]));
}

inline rcv_sync_and_neighbor_updated(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit) {
    bool process_this_message3 = true;
    if
    :: rcv_neighbor_boot_time > neighbor_boot_time[node_id] || (rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn > neighbor_snapshot_sn[node_id]) ->
        // if received greater BootTime or same BootTime and greater SnapshotSN... must resynchronize
        neighbor_boot_time[node_id] = rcv_neighbor_boot_time
        neighbor_snapshot_sn[node_id] = rcv_neighbor_snapshot_sn;
        current_sync_sn[node_id] = 0;
        process_this_message3 = false;
        if
        :: rcv_sync_sn == 0 && rcv_master_bit ->
            // if neighbor transmits message with SyncSN==0 and MasterBit set... consider neighbor as master
            my_snapshot_sn[node_id] = my_snapshot_sn[node_id] + 1;
            neighbor_state[node_id] = master;
            recv_sync_and_neighbor_is_master(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
        :: else ->
            // otherwise the node will consider itself as master
            new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
        fi;
    :: rcv_neighbor_boot_time < neighbor_boot_time[node_id] || (rcv_neighbor_boot_time == neighbor_boot_time[node_id] && rcv_neighbor_snapshot_sn < neighbor_snapshot_sn[node_id]) ->
        // if receive lower BootTime or same BootTime but with a lower SnapshotSN means that I have received a message from a previous sync process... must ignore this message
        process_this_message3 = false;
    :: else ->
        skip;
    fi;


    if
    :: process_this_message3 && rcv_sync_sn == current_sync_sn[node_id] && rcv_master_bit ->
        // if receive retransmission from Master... this means that I am slave and I already transitioned to Updated state while the neighbor node is still in a Non-Updated state because my last message has been lost
        // so I must retransmit my last message to Master
        ch[neighbor_id] ! sync(node_id, my_boot_time[node_id], neighbor_boot_time[node_id], my_snapshot_sn[node_id], neighbor_snapshot_sn[node_id], current_sync_sn[node_id], false, false);
    :: else ->
        skip;
    fi;
}

proctype Interface(byte node_id; byte my_initial_boot_time; byte my_initial_snapshot_sn; byte total_of_sync_msgs) {
  my_boot_time[node_id] = my_initial_boot_time;
  my_snapshot_sn[node_id] = my_initial_snapshot_sn;

  //byte neighbor_snapshot_sn = 0;
  //byte neighbor_boot_time = 0;

  mtype msg_type;
  byte neighbor_id;
  byte rcv_neighbor_boot_time;
  byte rcv_my_boot_time;
  byte rcv_neighbor_snapshot_sn;
  byte rcv_my_snapshot_sn;
  byte rcv_sync_sn;
  bool rcv_master_bit;
  bool rcv_more_bit;

      do
      :: nempty(ch[node_id]) && empty(fail_ch[node_id]) ->
      atomic {
        ch[node_id] ? msg_type(neighbor_id, rcv_neighbor_boot_time, rcv_my_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
        printf("neighbor_state: %e; msg_type: %e; neighbor_id: %d; rcv_neighbor_boot_time: %d; rcv_my_boot_time: %d, rcv_neighbor_snapshot_sn: %d; rcv_my_snapshot_sn: %d; rcv_sync_sn: %d; rcv_master_bit: %d; rcv_more_bit: %d\n", neighbor_state[node_id], msg_type, neighbor_id, rcv_neighbor_boot_time, rcv_my_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
        if
        :: msg_type == hello ->
            if
            :: neighbor_state[node_id] == unknown || (rcv_neighbor_boot_time > neighbor_boot_time[node_id]) ->
                  new_neighbor(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
            :: else ->
                  skip;
            fi;
        :: msg_type == sync ->
            if
            :: rcv_my_boot_time == my_boot_time[node_id] && neighbor_state[node_id] == unknown ->
                recv_sync_and_neighbor_is_unknown(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
            :: rcv_my_boot_time == my_boot_time[node_id] && neighbor_state[node_id] == master ->
                recv_sync_and_neighbor_is_master(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
            :: rcv_my_boot_time == my_boot_time[node_id] && neighbor_state[node_id] == slave ->
                recv_sync_and_neighbor_is_slave(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
            :: rcv_my_boot_time == my_boot_time[node_id] && neighbor_state[node_id] == updated ->
                rcv_sync_and_neighbor_updated(node_id, total_of_sync_msgs, neighbor_id, rcv_neighbor_boot_time, rcv_neighbor_snapshot_sn, rcv_my_snapshot_sn, rcv_sync_sn, rcv_master_bit, rcv_more_bit);
            :: else ->
                printf("ELSE\n");
                ch[neighbor_id] ! hello(node_id, my_boot_time[node_id], 0, 0, 0, 0, false, false);
                skip;
            fi;
        fi;
        }
        :: nempty(fail_ch[node_id]) ->
        atomic {
              fail_ch[node_id] ? (msg_type);
              if
              :: msg_type == reboot ->
                  printf("FAIL NODE %d\n", node_id);
                  neighbor_snapshot_sn[node_id] = 0;
                  neighbor_boot_time[node_id] = 0;
                  current_sync_sn[node_id] = 0;
                  neighbor_state[node_id] = unknown;
                  my_boot_time[node_id] = my_boot_time[node_id] + 1;
                  my_snapshot_sn[node_id] = 1;
                  ch[(node_id + 1) % 2] ! hello(node_id, my_boot_time[node_id], 0, 0, 0, 0, false, false);
              :: msg_type == broken_bidirectional_relationship ->
                  printf("BROKEN BIDIR NODE %d\n", node_id);
                  neighbor_snapshot_sn[node_id] = 0;
                  neighbor_boot_time[node_id] = 0;
                  current_sync_sn[node_id] = 0;
                  neighbor_state[node_id] = unknown;
                  my_snapshot_sn[node_id] = my_snapshot_sn[node_id] + 1;
              fi;}
      od;
}


init {
  byte total_msgs_of_process_0, total_msgs_of_process_1;
  select(total_msgs_of_process_0: 0 .. 2);
  printf("Node 0 requires %d Sync message to send all info\n", total_msgs_of_process_0);
  select(total_msgs_of_process_1: 0 .. 2);
  printf("Node 1 requires %d Sync message to send all info\n", total_msgs_of_process_1);
  TOTAL_MSGS_SYNC = total_msgs_of_process_0 + 1;
  if
  :: total_msgs_of_process_1 > total_msgs_of_process_0 ->
      TOTAL_MSGS_SYNC = total_msgs_of_process_1 + 1;
  :: else ->
      skip;
  fi;
  printf("In total are required %d Sync messages to complete synchronization\n", TOTAL_MSGS_SYNC);


	atomic{
      run Interface(0, 125, 12, total_msgs_of_process_0);
      run Interface(1, 15, 75, total_msgs_of_process_1);
	}

  // someone sends an Hello triggering the synchronization process
  atomic {
      if
      :: true ->
          ch[0] ! hello(1, 15, 0, 0, 0, 0, false, false);
      :: true ->
          ch[1] ! hello(0, 125, 0, 0, 0, 0, false, false);
      :: true ->
          ch[0] ! hello(1, 15, 0, 0, 0, 0, false, false);
          ch[1] ! hello(0, 125, 0, 0, 0, 0, false, false);
      fi;
  }

  atomic {
  if
  :: true ->
      fail_ch[0] ! reboot;
  :: true ->
      fail_ch[1] ! reboot;
  :: true ->
      fail_ch[0] ! reboot;
      fail_ch[1] ! reboot;
  :: true ->
      fail_ch[0] ! broken_bidirectional_relationship;
      ch[0] ! hello(1, my_boot_time[1], 0, 0, 0, 0, false, false);
  :: true ->
      fail_ch[1] ! broken_bidirectional_relationship;
      ch[1] ! hello(0, my_boot_time[0], 0, 0, 0, 0, false, false);
  :: true ->
      fail_ch[0] ! broken_bidirectional_relationship;
      fail_ch[1] ! broken_bidirectional_relationship;
      ch[0] ! hello(1, my_boot_time[1], 0, 0, 0, 0, false, false);
      ch[1] ! hello(0, my_boot_time[0], 0, 0, 0, 0, false, false);
  fi;
  }

  atomic {
  if
  :: true ->
      fail_ch[0] ! reboot;
  :: true ->
      fail_ch[1] ! reboot;
  :: true ->
      fail_ch[0] ! reboot;
      fail_ch[1] ! reboot;
  :: true ->
      fail_ch[0] ! broken_bidirectional_relationship;
      ch[0] ! hello(1, my_boot_time[1], 0, 0, 0, 0, false, false);
  :: true ->
      fail_ch[1] ! broken_bidirectional_relationship;
      ch[1] ! hello(0, my_boot_time[0], 0, 0, 0, 0, false, false);
  :: true ->
      fail_ch[0] ! broken_bidirectional_relationship;
      fail_ch[1] ! broken_bidirectional_relationship;
      ch[0] ! hello(1, my_boot_time[1], 0, 0, 0, 0, false, false);
      ch[1] ! hello(0, my_boot_time[0], 0, 0, 0, 0, false, false);
  fi;
  }
}

ltl ltl_test {(<>([](neighbor_state[0]==updated && neighbor_state[1]==updated && current_sync_sn[0]==TOTAL_MSGS_SYNC && current_sync_sn[1]==TOTAL_MSGS_SYNC && my_snapshot_sn[0]==neighbor_snapshot_sn[1] && my_snapshot_sn[1]==neighbor_snapshot_sn[0] && my_boot_time[0]==neighbor_boot_time[1] && my_boot_time[1]==neighbor_boot_time[0])))}