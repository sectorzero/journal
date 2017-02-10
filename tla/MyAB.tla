------------------------------ MODULE MyAB --------------------------------
EXTENDS Integers, Sequences

CONSTANT Data  \* The set of all possible data values.

RemoveFromSeq(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]
  
VARIABLES AVar,   \* The last <<value, bit>> pair A decided to send.
          BVar,    \* The last <<value, bit>> pair B received.
          ChannelAToB, \* FIFO Channel Lossy from A->B
          ChannelBToA \* FIFO Channel Lossy from A->B
          
TypeOK == /\ (AVar \in Data \X {0,1})
          /\ (BVar \in Data \X {0,1})
          /\ \A m \in ChannelAToB : m \in Data \X {0,1}
          /\ \A m \in ChannelBToA : m \in Data \X {0,1}

vars == << AVar, BVar, ChannelAToB, ChannelBToA >>

Init == /\ \E d \in Data: AVar = <<d, 1>>
        /\ BVar = AVar
        /\ ChannelAToB = <<>>
        /\ ChannelBToA = <<>>

ASend == /\ ChannelAToB' = Append(ChannelAToB, AVar)
         /\ UNCHANGED <<AVar, BVar, ChannelBToA>>

ARecv1 == /\ Len(ChannelBToA) # 0
          /\ Head(ChannelBToA) = AVar
          /\ ChannelBToA' = Tail(ChannelBToA)
          /\ \E d \in Data: AVar' = <<d, 1 - AVar[2]>>
          /\ UNCHANGED <<BVar, ChannelAToB>>

ARecv2 == /\ Len(ChannelBToA) # 0
          /\ Head(ChannelBToA) # AVar
          /\ ChannelBToA' = Tail(ChannelBToA)
          /\ UNCHANGED <<AVar, BVar, ChannelAToB>>       

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar
     /\ UNCHANGED <<ChannelAToB, ChannelBToA>>

BSend == /\ ChannelBToA' = Append(ChannelBToA, BVar)
         /\ UNCHANGED <<AVar, BVar, ChannelAToB>>

BRecv1 == /\ Len(ChannelAToB) # 0
          /\ Head(ChannelAToB) # BVar
          /\ BVar' = Head(ChannelAToB)
          /\ ChannelAToB' = Tail(ChannelAToB)   
          /\ UNCHANGED <<AVar, ChannelBToA>>

BRecv2 == /\ Len(ChannelAToB) # 0
          /\ Head(ChannelAToB) = BVar
          /\ ChannelAToB' = Tail(ChannelAToB)
          /\ UNCHANGED <<AVar, BVar, ChannelBToA>>       

DropChannelAToB == 
          /\ \E i \in 1..Len(ChannelAToB) : ChannelAToB' = RemoveFromSeq(i, ChannelAToB)
          /\ UNCHANGED <<AVar, BVar, ChannelBToA>>

DropChannelBToA == 
          /\ \E i \in 1..Len(ChannelBToA) : ChannelBToA' = RemoveFromSeq(i, ChannelBToA)
          /\ UNCHANGED <<AVar, BVar, ChannelAToB>>

Next == \/ ASend 
        \/ ARecv1
        \/ ARecv2
        \/ BSend
        \/ BRecv1
        \/ BRecv2
        \/ DropChannelAToB
        \/ DropChannelBToA

Spec == Init /\ [][Next]_vars

Inv == (AVar[2] = BVar[2]) <=> (AVar = BVar)
-----------------------------------------------------------------------------
FairSpec == Spec /\ WF_vars(Next) 
=============================================================================
\* Modification History
\* Last modified Wed Feb 08 12:04:48 PST 2017 by sectorzero
\* Last modified Wed Feb 08 11:04:26 PST 2017 by sectorzero
\* Last modified Mon Mar 21 17:41:40 PDT 2016 by lamport
\* Created Fri Sep 04 07:08:22 PDT 2015 by lamport

