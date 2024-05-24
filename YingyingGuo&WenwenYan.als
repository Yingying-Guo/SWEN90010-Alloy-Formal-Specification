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
	// send_counter [from][to] records the number of messages that Principal
	// 'from' has sent to Principal 'to' 
	var send_counter : Principal -> Principal -> one Int,

	// recv_counter [to][from] records the number of messages that Principal
	// 'to' has received from principal 'from'
	var recv_counter : Principal -> Principal -> one Int,
	var channel_state : one ChannelState,

	// the network can hold at most one message at a time
	var network : lone Message,

	// for debugging purposes (to aid reading counter - examples , etc .)
	// records the most recent action that has occurred
	var debug_last_action : lone DebugAction
}

// sender 'from' sends a message to receiver 'to' with sequence number
// 'seqnum ' and data 'd'
pred Send [from, to : Principal, seqnum : Int, d : Data ] {
	// ensure no message in the network
	no State.network
	
	// mock a message 
	( some m : Message | m.src = from and m.dest = to and m.seq_num = seqnum 
	and seqnum = State.send_counter [from,to] and m.data = d 
	and m in State.network')
	// update the send counter +1
	State.send_counter' = State.send_counter ++ ( from -> to -> (add[seqnum, 1]))
	State.recv_counter' = State.recv_counter
	State.channel_state' = State.channel_state

	// update the channel into sendAction
	State.debug_last_action' = SendAction
}

// receiver 'to' receives a message from sender 'from' with sequence number
// 'seqnum' and data 'd'
pred Recv [from , to : Principal , seqnum : Int , d : Data ] {
	// ensure one message in the network
	one State.network
	(some m : Message | 
		m.src = from and m.dest = to 
		and m.seq_num = seqnum 
		and seqnum = State.recv_counter[to, from] 
		and m.data = d 
		and m in State.network 
		and no State.network'
	)

	State.recv_counter' = State.recv_counter ++ ( to -> from -> (add[seqnum, 1]))
	State.send_counter' = State.send_counter
	State.channel_state' = State.channel_state
	State.debug_last_action' = RecvAction
}

// models the establishment of a secure channel
pred Go_Secure {
	no State.network
	State.channel_state = Insecure and State.channel_state' = Secure
// Task 2.1 fix the vulnerability (for check the fix, please comment the code in the following)  
	State.send_counter' = State.send_counter
	State.recv_counter' = State.recv_counter
//  Task 2.1 fix the vulnerability (for check the fix, please uncomment the code in the following)  
//	{
//		State.send_counter' = Principal -> Principal -> 0
//		and State.recv_counter' = Principal -> Principal -> 0
//	}
	
	State.network' = State.network
	State.debug_last_action' = GoSecureAction
}

pred Attacker_Action {
	// insecure opeartion includes remove , add, modify

	// When the channel is insecure, the attacker can remove, insert, or modify the message
	(some from, to: Principal, seqnum: Int, d: Data | State.channel_state = Insecure => (
		Attacker_RemoveMessage
		or Attacker_InsertIgnore[from, to, seqnum, d]
		or Attacker_ModifyMessage[from, to, seqnum, d])
	)
	and
	// When the channel is secure, the attacker can only remove the message
	(State.channel_state = Secure => Attacker_RemoveMessage)

	State.send_counter' = State.send_counter
	State.recv_counter' = State.recv_counter
	State.channel_state' = State.channel_state
	State.debug_last_action' = AttackerAction
}

pred Attacker_RemoveMessage{
	(State.channel_state = Insecure or State.channel_state = Secure)
	one State.network and no State.network'	
}

pred Attacker_InsertIgnore[from, to: Principal, seqnum: Int, d: Data] {
 	State.channel_state = Insecure and no State.network
	( some m : Message | m.src = from and m.dest = to and m.seq_num = seqnum 
		and seqnum = State.send_counter[from, to] and m.data = d 
		and m in State.network' and one State.network'
	)
}

pred Attacker_ModifyMessage[from, to: Principal, seqnum: Int, d: Data] {
	State.channel_state = Insecure and one State.network
	// after modified，m' still in the network and at least one of m' attributes does not match the corresponding attribute of m.
	(some m : Message | 
		(m in State.network and m.src = from and m.dest = to and m.seq_num = seqnum and m.data = d) 
			=> (m' in State.network' and (m'.src != from or m'.dest != to or m'.seq_num != seqnum or m'.data != d))
	)
}

// the initial state
pred Init {
	State.send_counter = Principal -> Principal -> 0
	State.recv_counter = Principal -> Principal -> 0
	State.channel_state = Insecure
	no State.network
	no State.debug_last_action
}

pred State_Transition {
( some from, to : Principal, seqnum : Int, d : Data |
	Send [from, to, seqnum, d] or Recv [from, to, seqnum, d])
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

assert sendRecv {
	always all from, to : Principal, seqnum: Int, d: Data |
	(Send[from, to, seqnum, d]; Attacker_Action; Recv[from, to, seqnum, d]) 
		=> State.send_counter[from, to] = State.recv_counter[to, from]
}

// for check the attack action
pred send_and_attack {
	no State.network
	(some from, to : Principal, seqnum : Int, d : Data |
	Send [from, to, seqnum, d] and after Attacker_ModifyMessage[from, to, seqnum, d])
}

assert is_sync_always {
	always all from, to : Principal |
	(State.debug_last_action = RecvAction) =>
	(State.send_counter[from, to] = State.recv_counter[to, from]) 
}
check is_sync_always for 2 but 3..10 steps expect 1
// Task 1.2 Explanation: 
// 	When there is no message on the network, it can only execute the SendAction or Insert ignore action by the attacker.
// 	If the RecvAction received the message from the attacker, 
// 	The recv_counter will plus 1 while the send_counter won't change.
// 	In this case, the send_couner and recv_counter won't equal after the RecvAction was already called.

assert is_sync {
	always all from, to : Principal |
	(State.debug_last_action = RecvAction and no State.network
		and (historically AttackerAction not in State.debug_last_action)
	) => (State.send_counter[from, to] = State.recv_counter[to, from]) 
}
check is_sync for 2 but 3..10 steps expect 0
// Task 1.3 Explanation：
// 	If the AttackerAction doesn't occur, the message will be only operated by the SendAction and RecvAction 
// 	And when there is no message in the network, 
// 	It will keep the receiver’s send and receive counters for the sender mirror the sender’s for the receiver.

assert security_goal {
	always all a: Principal, b: Principal, seqnum1, seqnum2: Int, d: Data |
	(
		(Send[a, b, seqnum2, d] and after State.channel_state = Secure)
	) 
	=> (
		eventually(Send[a, b, seqnum2, d] and State.channel_state = Secure)
		=> eventually(Recv[a, b, seqnum1, d] and State.channel_state = Secure)
		=> eventually(Recv[a, b, seqnum2, d] and State.channel_state = Secure)
	)
}

// Task 1.4 Vulnerability:
// 	The counterexample shows before Go_Secure action, it will receive a message that the attacker's InsertIgnore action inserted.
// 	and the attacker will remove the m1 sent from the sender, then the receiver will receive the m2.
// 	So that it not receive in order.

// 	It is the prefix truncation attack. 
// 	Because an ignore message was inserted earlier, the client still ends up receiving the expected number of received messages, 
// 	While the server thinks it has sent the correct number of messages.

// check the security goal without fixing the vulnerability
check security_goal for 2 but 3..10 steps expect 1

// check the security goal after fixing the vulnerability
check security_goal for 2 but 3..15 steps expect 0

// Task 2.1
// 	Fix description:
// 	We modified the operations of the send_counter and recv_counter in the Go_Secure predicate:
//		{
//			State.send_counter' = Principal -> Principal -> 0
//			and State.recv_counter' = Principal -> Principal -> 0
//		} 
//	To reset the send_counter and recv_counter to 0 in the Go_Secure predicate.
//	Please follow the instruction to uncommect and comment the codes if you want to check the fix

// Task 2.2 Explanation:
// 	We decided to check the counterexample range from 3 to 15, 
// 	As we analyze the prefix truncation attack and reckon that the counterexample needs 9 steps to detect
// 	It should at least contain SendAction, RecvAction for 4 steps and AttackerAction for 2 steps and 1 step of Go_Secure.
// 	And for ensuring that we still hold the security goal if there are other attacker actios performed,
//	So we set the upper boundary into 15 steps to check the assertion.



//Task 2.3
// Limitations and Vulnerabilities:

// (It would be so long to see the answer, you can glance the summary first :) )

// The details analysis as follows:
// There are 3 types of these attacks existed in the CVE database[1][2]. Now we analyze whether these attacks could be caught by this Model: 

// 1. CVE-2023-48795(a.k.a. Terrapin Attack, including Prefix Truncation Attack on the BPP and Extension Information Downgrade Attack) [3]: 
// This CVE identifies flaws in the way in which the SSH protocol is implemented in the BPP negotiation process at the time of establishing system-to-system communication known as handshaking. 
// The way in which SSH sequence numbers and confidential checkups lack of checking is the primary problem. This allows attackers to bypass security features by tampering (modifying, deleting or inserting) with the mechanisms. 

// 2. CVE-2023-46445 (a.k.a. Rogue Extension Negotiation Attack) [4]: 
// This CVE allows an attacker to control extended information messages through man-in-the-middle attacks.

// 3. CVE-2023-46446 (a.k.a. Rogue Session Attack) [5]: 
// This CVE enables session injection before keys have been fully exchanged and set up, 
// meaning that an attacker may send a simple authentication mechanism password or public key without further exchange.

// Analysis: 
// 1.	For CVE-2023-48795 [3], we can we try to assume attack steps：

// 1.1 Initiate SSH Connection：
// An attacker initiated a connection to an SSH server with a client that had been modified to exploit such vulnerabilities.

// 1.2 Inject malicious SSH MSG KEXINIT：
// During handshaking, specifically, when SSH_MSG_KEXINIT messages are exchanged, 
// an attacker replaced parts of the payload of these or other messages or omitted some packets or change the order or content of extended negotiation messages.

// 1.3 Server processes modified packet and then Security downgraded：
// Because of the illegitimately manipulated messages are allowed to be processed in this way that they avoid the correctness checks that 
// SSH does assure the endpoints of the connection to be agreed to set security parameters.

// 1.4 Establish SSH session (compromised)：
// The server is forced by tampered negotiation to agree upon a set of parameters from which a few features 
// such as certain encryption algorithms or correctness checks from the server’s usual features were omitted.

// 1.5 Exploitation：
// As a result of connection to a compromised security condition, an attacker could now decrypt, modify, or change the path of the data without SSH protection.

// The attacker in STEP 2 changes the payload to change the order or contents of the extended negotiation messages. 
// This entails changing the sequence numbers, which in the actual case, if modified rather than incremented or decremented, 
// the packets altered will not be on the expected sequence number hence flagged When this happens, the changed packet is tagged as a legitimate and genuine packet, 
// while in actuality, it is not, Article However, since the Alloy model is only majoring on secure communication and matter to do with the state transition, 
// it does not handle SSH integrity checking in its operation. 
// In STEP 3, the model did not offers on a simulation of packet integrity, 
// hence detecting discrepancies in packet integrity that arise in the process thus being used in completion of other connections.

// 2.	For CVE-2023-46445 [4] or CVE-2023-46446 [5]：

// These attacks refer to imperfections in the encryption, session key exchange or authentication made in SSH. 
// Thus, the Alloy model must integrate a comprehensive simulation of the functionality of SSH encryption, how keys are exchanged, regulated and authenticated. 
// Nonetheless, contemporary setups of models dependent on message passing and state transitions of channel perform may fail to recognize these vulnerabilities 
// due to the required cryptographic sophistication unless their failure or cryptographic operations are modeled explicitly.


// Summary at here:
// For below-known prefix truncation attack, we find that although the simplified Alloy model can detect some prefix truncation attack, the known attack under the CVE database model occurs. 

// The alloy model cannot fully detect the vulnerability of the Terrapin Attack (CVE-2023-48795). 
// As it just checks the correctness of sequence numbers but lacks of the simulation of packet integrity, 
// these cannot check the security in the security of Server processes modified packet and then Security downgraded.

// In the other sides, the alloy model also cannot detect the vulnerability of Rogue Extension Negotiation Attack (CVE-2023-46445) and Rogue Session Attack (CVE-2023-46446), 
// as these attacks refer to imperfections in the encryption, session key exchange or authentication made in SSH. 
// And the model did not simulate these actions.


//Reference list
//[1] Bäumer, F 2024, Terrapin Attack, Terrapin-attack.com, viewed 19 April 2024, <https://terrapin-attack.com/>.
//[2] Bäumer, F, Brinkmann, M & Schwenk, J 2023, Terrapin Attack: Breaking SSH Channel Integrity By Sequence Number Manipulation, arXiv.org, viewed 19 April 2024, <https://arxiv.org/abs/2312.12422>.
//[3] Canonical Ubuntu 2023c, CVE-2023-48795 | Ubuntu, Ubuntu, viewed 19 April 2024, <https://ubuntu.com/security/CVE-2023-48795>.
//[4] Canonical Ubuntu 2023a, CVE-2023-46445 | Ubuntu, Ubuntu, viewed 19 April 2024, <https://ubuntu.com/security/CVE-2023-46445>.
//[5] Canonical Ubuntu 2023b, CVE-2023-46446 | Ubuntu, Ubuntu, viewed 19 April 2024, <https://ubuntu.com/security/CVE-2023-46446>.







