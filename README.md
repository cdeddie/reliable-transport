# reliable-transport

- Only transfer from A to B is required. B will still need to send packets to A for ACK
- tolayer3() indicates sending across network layer

### Go Back N API
- A_output(struct msg message): Function called when upper layer at A has a message to send
- A_input(struct pkt packet): Function called when packet sent from B arrives at A
- A_timerinterrupt(): Called when A's timer expires, controlling the retransmission of packets

### Emulator
- A loss/corruption of 0.1 means 1 in 10 packets avg are lost
- Contents of payload, sequence or ack field can be corrupted


### Changes
- Instead of cumultative ACKs each packet gets its own ACK
- Only retransmit specific packets that timeout, not entire window
- Receiver must buffer out of order packets
- Receiver sends the ACK related to the packet, not the base ACK
- Only slide window when oldest packet is ACKed

- Only have one timer and no way to get simulated time
    - Time the oldest unACKed packet (packet at base)
    - When that packet times out, retransmit it and restart timer
    - If a packet gets ACKed and it was the timed packet, move timer to next oldest unACKed packet

- A_output():
    - Track individual ACKs
    - Only start timer if this is first unacked packet

- A_input():
    - Handle individual ACKs instead of cumulative
    - Mark specific packets as ACKed
    - Slide window when possible
    - Restart timer for next oldest unacked packet

- A_timerinterrput():
    - Retransmit only the timed packet (oldest unacked)
    - Restart timer for same packet

- B_input():
    - Accept packets in any order within window
    - Buffer out of order packets
    - Send individual ACKs for each receieved packet