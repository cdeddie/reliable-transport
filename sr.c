#include "emulator.h"
#include "sr.h"
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

/* ******************************************************************
   Selective repeat protocol.
**********************************************************************/

#define RTT 16.0 /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6 /* the maximum number of buffered unacked packet                          
      MUST BE SET TO 6 when submitting assignment */
#define SEQSPACE 12 /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1) /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender
   and receiver the simulator will overwrite part of your packet with 'z's.  It
   will not overwrite your original checksum.  This procedure must generate a
   different checksum to the original if the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
    int checksum = 0;
    int i;

    checksum = packet.seqnum;
    checksum += packet.acknum;
    for (i = 0; i < 20; i++)
    {
        checksum += (int)(packet.payload[i]);
    }

    return checksum;
}

bool IsCorrupted(struct pkt packet)
{
    if (packet.checksum == ComputeChecksum(packet)) return (false);
    else return (true);
}

/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE]; /* array of struct pkt for storing packets waiting for ACK */
static bool acked[SEQSPACE];
static int windowfirst, windowlast; /* array indexes of the first/last packet awaiting ACK */
static int windowcount;  /* the number of packets currently awaiting an ACK */
static int A_nextseqnum; /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to
 * other side */
void A_output(struct msg message)
{
    struct pkt sendpkt;
    int i;

    /* If window is not full, then we can send, otherwise need to wait for ACK
    * from B to free up space */
    if (windowcount < WINDOWSIZE) {
        if (TRACE > 1)
        printf("----A: New message arrives, send window is not full, send new "
                "messge to layer3!\n");

        /* create packet */
        sendpkt.seqnum = A_nextseqnum;
        sendpkt.acknum = NOTINUSE;
        for (i = 0; i < 20; i++)
        {
            sendpkt.payload[i] = message.data[i];
        }
        sendpkt.checksum = ComputeChecksum(sendpkt);

        /* put packet in window buffer */
        windowlast = (windowlast + 1) % WINDOWSIZE;
        buffer[windowlast] = sendpkt;
        acked[A_nextseqnum] = false;
        windowcount++;

        /* send out packet */
        if (TRACE > 0)
            printf("----A: Sending packet %d to layer 3\n", sendpkt.seqnum);

        tolayer3(A, sendpkt);

        /* start timer if first unACKed packet in window */
        if (windowcount == 1)
            starttimer(A, RTT);

        /* advance next seq number */
        A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
    }
    /* if blocked,  window is full */
    else
    {
        if (TRACE > 0)
            printf("----A: New message arrives, send window is full\n");
        window_full++;
    }
}

/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
    if (IsCorrupted(packet))
    {
        if (TRACE > 0)
        printf("----A: corrupted ACK is received, do nothing!\n");
        return;
    }

    if (TRACE > 0)
    {
        printf("----A: uncorrupted ACK %d is received\n", packet.acknum);
    }

    total_ACKs_received++;

    int ack_index = packet.acknum;

    /* mark specific ack sequence number as ACKed */
    if ( ((ack_index - buffer[windowfirst].seqnum + SEQSPACE) % SEQSPACE) < windowcount && !acked[ack_index])
    {
        acked[ack_index] = true;
        new_ACKs++;
        if (TRACE > 0)
        {
            printf("----A: new ACK %d is received\n", packet.acknum);
        }
    }
    else
    {
        if (TRACE > 0)
        {
            printf("----A: duplicate ACK %d is received\n", packet.acknum);
        }
        return;
    }

    /* slide window if possible */

    while (windowcount > 0 && acked[buffer[windowfirst].seqnum])
    {
        acked[buffer[windowfirst].seqnum] = false;
        windowfirst = (windowfirst + 1) % WINDOWSIZE;
        windowcount--;
    }

    /* reset values when window is empty */
    if (windowcount == 0)
    {
        windowfirst = 0;
        windowlast = -1;
    }

    /* start timer if there are more unACKed packets in the window */
    stoptimer(A);
    if (windowcount > 0)
    {
        starttimer(A, RTT);
    }
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
    if (TRACE > 0)
        printf("----A: time out, resend oldest unACKed packet!\n");

    tolayer3(A, buffer[windowfirst]);
    packets_resent++;
    starttimer(A, RTT);
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void) {
    /* initialise A's window, buffer and sequence number */
    A_nextseqnum = 0; /* A starts with seq num 0, do not change this */
    windowfirst = 0;
    windowlast = -1;
    int i;
    for (i = 0; i < WINDOWSIZE; i++)
    {
        acked[i] = false;
    }
    windowcount = 0;
}

/********* Receiver (B)  variables and procedures ************/

static int expectedseqnum; /* the sequence number expected next by the receiver */
static int B_nextseqnum; /* the sequence number for the next packets sent by B */
static struct pkt B_buffer[SEQSPACE];
static bool received[SEQSPACE];

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet) {
    if (IsCorrupted(packet))
    {
        if (TRACE > 0)
        {
            printf("----B: corrupted packet %d is received, do nothing\n", packet.seqnum);
        }
        return;
    }

    /* check if packet is within reciever window */
    int seqnum = packet.seqnum;

    /* check if packet is in recv window */
    if ( ((seqnum - expectedseqnum + SEQSPACE) % SEQSPACE) < WINDOWSIZE && !received[seqnum]) {
        /* new packet */
        received[seqnum] = true;
        B_buffer[seqnum] = packet;
        packets_received++;

        if (TRACE > 0)
        {
            printf("----B: new packet %d is received, send ACK\n", seqnum);
        }
    }
    else if (received[seqnum])
    {
        /* duplicate packet */
        if (TRACE > 0)
        {
            printf("----B: duplicate packet %d is received", seqnum);
        }
    }
    else
    {
        /* packet is outside window */
        if (TRACE > 0)
        {
            printf("----B: packet %d outside window, ignored", seqnum);
        }
        return;
    }

    /* send ACK for specific packet */
    struct pkt sendpkt;
    sendpkt.acknum = seqnum;
    sendpkt.seqnum = B_nextseqnum;
    B_nextseqnum = (B_nextseqnum + 1) % 2;
    int i;
    for (i = 0; i < 20; i++)
    {
        sendpkt.payload[i] = '0';
    }
    sendpkt.checksum = ComputeChecksum(sendpkt);
    tolayer3(B, sendpkt);

    /* deliver packets to layer 5 in order */
    while (received[expectedseqnum % SEQSPACE])
    {
        tolayer5(B, B_buffer[expectedseqnum].payload);
        received[expectedseqnum % SEQSPACE] = false;
        expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
    }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
    expectedseqnum = 0;
    B_nextseqnum = 1;
    int i;
    for (i = 0; i < WINDOWSIZE; i++)
    {
        B_buffer[i].seqnum = NOTINUSE;
        received[i] = false;
    }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message) {}

/* called when B's timer goes off */
void B_timerinterrupt(void) {}
