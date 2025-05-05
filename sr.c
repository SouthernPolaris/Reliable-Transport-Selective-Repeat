#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "gbn.h"

/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2  

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications: 
   - removed bidirectional GBN code and other code not used by prac. 
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet */
#define SEQSPACE 16      /* the min sequence space for Selective Repeat must be at least windowsize * 2 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */
#define WINDOWFULLBUFFERSIZE 100

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

/* Buffer needs to be of len SEQSPACE for proper implementation */
static struct pkt buffer[SEQSPACE];  /* array for storing packets waiting for ACK */
static int windowfirst;            /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */
static bool isAcked[SEQSPACE];

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if valid window */
  if (windowfirst + WINDOWSIZE > A_nextseqnum) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for ( i=0; i<20 ; i++ ) 
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt); 

    /* put packet in window buffer */
    buffer[A_nextseqnum % SEQSPACE] = sendpkt;
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    /* send out packet */
    tolayer3 (A, sendpkt);

    if (A_nextseqnum == windowfirst) {
      /* start timer if first packet in window */
      starttimer(A,RTT);
    }

    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;

  } else {
    if (TRACE > 0) {
      printf("----A: New message arrives, send window is full\n");
    }
    window_full++;
  }
}

/* check if sequence number is within window */
bool is_within_window(int seqnum, int start, int end) {
  if (start <= end) {
      return seqnum >= start && seqnum < end;
  } else {
      return seqnum >= start || seqnum < end;
  }
}

/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
  if (IsCorrupted(packet)) {
    if (TRACE > 0) {
      printf("----A: corrupted ACK is received, do nothing!\n");
    }
    return;
  }

  total_ACKs_received += 1;
  if (TRACE > 0) {
    printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
  }

  if (!is_within_window(packet.acknum, windowfirst, A_nextseqnum)) {
    return;
  }

  if (isAcked[packet.acknum]) {
    if (TRACE > 0) {
      printf("----A: duplicate ACK %d, do nothing!\n", packet.acknum);
    }
    return;
  }
   
  new_ACKs++;
  
  if (TRACE > 0) {
    printf("----A: ACK %d is not a duplicate\n", packet.acknum);
  }
  
  isAcked[packet.acknum] = true;

  if (packet.acknum == windowfirst) {
    stoptimer(A);

    while (windowfirst != A_nextseqnum && isAcked[windowfirst] == true) {
      isAcked[windowfirst] = false;
      windowfirst = (windowfirst + 1) % SEQSPACE;
    }

    if (windowfirst != A_nextseqnum) {
      starttimer(A, RTT);
    }
  }

}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  struct pkt send_pkt;
  
  send_pkt = buffer[windowfirst];

  if (TRACE > 0) {
    printf("----A: time out,resend packets!\n");
    printf("---A: resending packet %d\n", (send_pkt.seqnum));
  }

  /* Singular packet sending only instead of GBN's for loop as sends packets individually instead of all after */
  tolayer3(A, send_pkt);
  packets_resent++;
  starttimer(A, RTT);
}       



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  int i;
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0; 
  windowfirst = 0;

  for (i = 0; i < SEQSPACE; i++) {
    isAcked[i] = false;
  }
}



/********* Receiver (B)  variables and procedures ************/

static int expectedseqnum; /* the sequence number expected next by the receiver */
static int B_nextseqnum;   /* the sequence number for the next packets sent by B */
static struct pkt buffer_B_side[SEQSPACE];
static int buffer_B_start;

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt buffer_pkt;
  int i;

  bool currWindow = false;
  int left = buffer_B_start;
  int right = (buffer_B_start + WINDOWSIZE) % SEQSPACE;

  bool prevWindow = false;
  int prevLeft = (buffer_B_start + SEQSPACE - WINDOWSIZE) % SEQSPACE;
  int prevRight = buffer_B_start;

  if (IsCorrupted(packet)) {
    return;
  }

  if (TRACE > 0)
    printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
  packets_received++;

  currWindow = is_within_window(packet.seqnum, left, right);

  if (currWindow) {
    struct pkt packet_return;
    packet_return.seqnum = NOTINUSE;
    packet_return.acknum = packet.seqnum;

    for (i = 0; i < 20; i++) {
      packet_return.payload[i] = 'A';
    }
    packet_return.checksum = ComputeChecksum(packet_return);

    tolayer3(B, packet_return);

    buffer_pkt = buffer_B_side[packet.seqnum];

    if (buffer_pkt.seqnum == NOTINUSE) {
      buffer_B_side[packet.seqnum] = packet;
    }

    while (buffer_B_side[buffer_B_start].seqnum != NOTINUSE) {
      tolayer5(B, buffer_B_side[buffer_B_start].payload);
      buffer_B_side[buffer_B_start].seqnum = NOTINUSE;
  
      /* Slide the window forward */
      buffer_B_start = (buffer_B_start + 1) % SEQSPACE;
  }
    return;
  }

  prevWindow = is_within_window(packet.seqnum, prevLeft, prevRight);

  if (prevWindow) {
    struct pkt prev_buffer_pkt;
    prev_buffer_pkt.seqnum = NOTINUSE;
    prev_buffer_pkt.acknum = packet.seqnum;
    for (i = 0; i < 20; i++) {
      prev_buffer_pkt.payload[i] = 'A';
    }
    prev_buffer_pkt.checksum = ComputeChecksum(prev_buffer_pkt);
    tolayer3(B, prev_buffer_pkt);
  }
}
/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  int seq_item;
  int idx;
  expectedseqnum = 0;
  B_nextseqnum = 1;

  buffer_B_start = 0;

  for (seq_item = 0; seq_item < SEQSPACE; seq_item++) {
    buffer_B_side[seq_item].acknum = NOTINUSE;
    buffer_B_side[seq_item].seqnum = NOTINUSE;
    /* fill the buffer with 0's */
    for (idx = 0; idx < 20; idx++) {
      buffer_B_side[seq_item].payload[idx] = '0';
    }
  }
}
/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}

