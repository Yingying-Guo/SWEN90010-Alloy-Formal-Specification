sig Principal {}

sig Data {}

sig Message {
  seq_num : one Int,
  src : one Principal,
  dest : one Principal,
  data : one Data
}

abstract sig ChannelState {}
one sig Insecure, Secure extends ChannelState {}

abstract sig DebugAction {}
one sig SendAction, RecvAction, AttackerAction, GoSecureAction extends DebugAction {}

one sig State {
  // send_counter[from][to] records the number of messages that Principal 'from' has sent
  // to Principal 'to'
  var send_counter : Principal -> Principal -> one Int,
  // recv_counter[to][from] records the number of messages that Principal 'to' has received
  // from principal 'from'
  var recv_counter : Principal -> Principal -> one Int,

  var channel_state : one ChannelState,
  // the network can hold at most one message at a time
  var network : lone Message,
  // for debugging purposes (to aid reading counter-examples, etc.)
  // records the most recent action that has occurred
  var debug_last_action : lone DebugAction
}

// the initial state
pred Init {
  State.send_counter  = Principal -> Principal -> 0
  State.recv_counter  = Principal -> Principal -> 0
  State.channel_state =  Insecure
  no State.network
  no State.debug_last_action
}

// sender 'from' sends a message to receiver 'to' with sequence number 'seqnum' and data 'd'
pred Send[from, to : Principal, seqnum : Int, d : Data] {
  no State.network
  (some m : Message | m.src = from and m.dest = to and m.seq_num = seqnum and 
    seqnum = State.send_counter[from,to] and m.data = d and 
    m in State.network')
  State.send_counter' = State.send_counter ++ (from -> to -> (add[seqnum,1]))
  State.recv_counter' = State.recv_counter
  State.channel_state' = State.channel_state
  State.debug_last_action' = SendAction
}

// Task 1.1 (Recv)
// receiver 'to' receives a message from sender 'from' with sequence number 'seqnum' and data 'd'
pred Recv[from, to : Principal, seqnum : Int, d : Data] {
  some m : Message | m in State.network and m.src = from and m.dest = to and m.seq_num = seqnum and m.data = d
  State.recv_counter[to,from] = seqnum
  State.send_counter' = State.send_counter
  State.recv_counter' = State.recv_counter ++ (to -> from -> (add[seqnum,1]))
  no State.network'
  State.channel_state' = State.channel_state
  State.debug_last_action' = RecvAction
}

// models the establishment of a secure channel 
pred Go_Secure {
  no State.network // this is important so that we don't go secure after attacker has injected a msg
  State.channel_state = Insecure and State.channel_state' = Secure
  
  State.network' = State.network
  State.debug_last_action' = GoSecureAction

  State.send_counter' = State.send_counter
  State.recv_counter' = State.recv_counter
  // Task 2.1 a fix for the attack -- we reset everyone's sequence numbers at once
  // consistent with the abstraction that we only model one secure channel
  // comment the above 2 lines and uncomment the following 2 lines to fix
  // State.send_counter' = Principal -> Principal -> 0
  // State.recv_counter' = Principal -> Principal ->  0

}

// Task 1.1 (Attack Action)
pred Attacker_Action {
  // can only drop messages in secure state (no replays etc. to keep it simple)
  (Secure in State.channel_state implies (State.network' in State.network))
  State.send_counter' = State.send_counter
  State.recv_counter' = State.recv_counter
  State.channel_state' = State.channel_state
  State.debug_last_action' = AttackerAction
}

// Task 1.1 (Attack Action, another solution)
// Other correct solutions should be equivalent to one of these two
pred Attacker_Action2 {
  // can only drop messages in secure state (no replays etc. to keep it simple)
  (Secure in State.channel_state implies (State.network' in State.network))
  // the previous predicate allows State.network unchanged.
  // Adding this line will disallow it. Both solutions are correct.
  State.network' != State.network
  State.send_counter' = State.send_counter
  State.recv_counter' = State.recv_counter
  State.channel_state' = State.channel_state
  State.debug_last_action' = AttackerAction
}

pred State_Transition {
  (some from, to : Principal, seqnum : Int, d : Data | Send[from,to,seqnum,d] or Recv[from,to,seqnum,d])
  or
  Go_Secure
  or
  Do_Nothing
  or
  Attacker_Action
}

pred Do_Nothing {
  State.send_counter' = State.send_counter
  State.recv_counter' = State.recv_counter
  State.network' = State.network
  State.channel_state' = State.channel_state
  no State.debug_last_action'
}



// constrain traces
fact traces {
  Init and
  (always State_Transition)
}

// Task 1.2
assert in_sync_always {
  always { all from, to : Principal, seqnum : Int, d : Data | 
     Recv[from,to,seqnum,d] implies {
     State.send_counter'[from,to] = State.recv_counter'[to,from] and
     State.recv_counter'[from,to] = State.send_counter'[to,from]
    }
  }
}

check in_sync_always for 2 but 2 Principal, 1..8 steps expect 1

// Task 1.3 Correct condition: In Secure
assert in_sync {
  always { all from, to : Principal, seqnum : Int, d : Data |  
    (Secure in State.channel_state and Recv[from,to,seqnum,d]) implies {
     State.send_counter'[from,to] = State.recv_counter'[to,from] and
     State.recv_counter'[from,to] = State.send_counter'[to,from]
    }
  }
}

// this should always be true. If we receive a message in Secure mode,
// then it had to be sent by the legitimate party and, moreover, it is
// the most recent message that that party sent. The reason is that 
// in Secure mode, messages can only be dropped (but e.g. not replaying old ones).
// If it was the most recent sent by the sender to us then we know
// the sender's send_count is equal to its seqnum. After we receive it,
// we increment our recv_count for that sender. So the two will now match.
//
// TODO: consider allowing message replay from the attacker even in secure mode.
//            that would break this property for sure.
// If we dont do that, get them to explain why this property should always be true
// under the attacker model.
check in_sync for 3 but 2 Principal, 1 Data, 8..8 steps expect 0

// this is not a counter-example because we never go secure.
run desync {
  some from, to : Principal, d : Data | {
  Send[from,to,0,d] ;
  Attacker_Action ;
  no State.network and Send[from,to,1,d] ;
  Attacker_Action ;
  Recv[from,to,0,d] }
}


// Task 1.4 (Security goal)
// There are many possible solutions for this task. 
// Some marks may be deducted if the assertion is very hard coding.

// the absence of prefix-truncation property
assert no_prefix_truncation {
always  {
  State.channel_state = Secure implies
  (all from, to : Principal, seqnum : Int, d : Data | {
     Send[from,to,seqnum,d] implies (always { all seqnum2 : Int, d2 : Data | {
      (seqnum2 > seqnum and Recv[from,to,seqnum2,d2]) implies (once Recv[from,to,seqnum,d] and State.channel_state = Secure)
      }
      })
  }
  )
}}

/*
 A prefix truncation attack:

 AttackerAction:    * attacker fakes msg from Alice to Bob w/ seq_num 0
 RecvAction: msg received by Bob, Bob's recv_count for Alice is 1
 Go Secure
 SendAction Alice sends msg to Bob with seq_num 0 (Alice's send_count for Bob is 1)
 AttackerAction msg gets dropped
 SendAction Alice sends msg to Bob with seq_num 1 (Alice's send_count for Bob is 2)
 RecvAction Bob receives msg with seq_num 1 (matches his recv_count for Alice)
*/

// Task 2.2
check no_prefix_truncation for 3 but 5 Message, 2 Principal, 2 Data, 12..12 steps expect 1


// Task 2.3
// The choice to model everyone going secure together (not just the two participants in the
// protocol to that point) means that we would be unable to detect attacks that might arise
// when multiple sessions of the protocol involving more than two principals might somehow
// interact, or even when multiple concurrent sessions between the *same* two principals
// might interact. For instance, the protocol might be secure when only ever run once
// between a single pair of participants, but it migth have a flaw that could arise if the
// protocol is then run a second time involving a third participant. An example of this
// kind of flaw is in the Needham Schroeder Public Key protocol, found by Gavin Lowe
// see e.g. https://www.cs.utexas.edu/~shmat/courses/cs6431/lowe.pdf
// (Actually this model only works for one Principle.)
