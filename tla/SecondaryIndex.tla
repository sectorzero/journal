--------------------------------- MODULE SecondaryIndex ---------------------------------
(***************************************************************************)
(* This module specifies the Paxos Commit algorithm.  We specify only      *)
(* safety properties, not liveness properties.  We simplify the            *)
(* specification in the following ways.                                    *)
(*                                                                         *)
(*  - As in the specification of module TwoPhase, and for the same         *)
(*    reasons, we let the variable msgs be the set of all messages that    *)
(*    have ever been sent.  If a message is sent to a set of recipients,   *)
(*    only one copy of the message appears in msgs.                        *)
(*                                                                         *)
(*  - We do not explicitly model the receipt of messages.  If an           *)
(*    operation can be performed when a process has received a certain set *)
(*    of messages, then the operation is represented by an action that is  *)
(*    enabled when those messages are in the set msgs of sent messages.    *)
(*    (We are specifying only safety properties, which assert what events  *)
(*    can occur, and the operation can occur if the messages that enable   *)
(*    it have been sent.)                                                  *)
(*                                                                         *)
(*  -  We do not model leader selection.  We define actions that the       *)
(*    current leader may perform, but do not specify who performs them.    *)
(*                                                                         *)
(* As in the specification of Two-Phase commit in module TwoPhase, we have *)
(* RMs spontaneously issue Prepared messages and we ignore Prepare         *)
(* messages.                                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT REQUESTS, INDEXERS

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]
  
\* TODO
Last(seq) ==
    Head(seq)

-----------------------------------------------------------------------------
VARIABLES Pri,          \* Primary Table Log Of Updates For A Single Key,
          WrkQ,         \* Updates Hint Queue,
          Idx,          \* Idx[Value] Index Table,
          RState,       \* RState[r] Requests State
          IState        \* IState[i] Indexers State

vars == <<Pri, WrkQ, Idx, RState, IState>>

SIdxInit == /\ Pri = << [etag |-> 0, val |-> "initial"] >>
        /\ WrkQ = << >>
        /\ Idx = { [etag |-> 0, val |-> "initial"] } 
        /\ RState = [r \in REQUESTS |-> [ state |-> "queued", retag |-> 0, rval |-> r] ] 
        /\ IState = [i \in INDEXERS |-> [ state |-> "waiting", etagold |-> 0, rvalold |-> ""] ]
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                THE ACTIONS                              *)
(***************************************************************************)
Process_2_3(r) ==
        (*************************************************************************)
        (* Resource manager r prepares by sending a phase 2a message for ballot  *)
        (* number 0 with value "prepared".                                       *)
        (*************************************************************************)
        /\ RState[r].state = "queued"
        /\ RState' = [RState EXCEPT ![r] = [state |-> "read", retag |-> Last(Pri).etag, rval |-> Head(Pri).val]]
        /\ UNCHANGED <<Pri, WrkQ, Idx, IState>>

Process_4_5(r) == 
        /\ RState[r].state = "read"
        /\ WrkQ' = Append(WrkQ, [etagold |-> RState[r].retag, valold |-> RState[r].rval])
        /\ RState' = [RState EXCEPT ![r] = [state |-> "hinted"]]
        /\ UNCHANGED <<Pri, Idx, IState>>

Process_6_7(r) == 
        /\ RState[r].state = "hinted"
        /\ Pri' = Append(Pri, [etag |-> Last(Pri).etag + 1, val |-> r])
        /\ RState' = [RState EXCEPT ![r] = [state |-> "updated"]]
        /\ UNCHANGED <<WrkQ, Idx, IState>>

IndexerRetrieveHint(i) == 
        /\ IState[i].state = "waiting"
        /\ Len(WrkQ) > 0
        /\ IState' = [IState EXCEPT ![i] = [ state |-> "idx1", etagold |-> Head(WrkQ).etagold, valold |-> Head(WrkQ).valold]]
        /\ WrkQ' = Tail(WrkQ)
        /\ UNCHANGED <<Pri, Idx, RState>>

IndexerReadPrimaryTable(i) ==
        /\ IState[i].state = "idx1"
        /\ \/ /\ IState[i].etagold >= Last(Pri).etag
              /\ IState' = [IState EXCEPT ![i] = [state |-> "idx2", etanew |-> Last(Pri).etag, valnew |-> Last(Pri).val]]
           \/ /\ IState' = [IState EXCEPT ![i] = [state |-> "waiting", etagold |-> 0, rvalold |-> ""]]             
        /\ UNCHANGED <<Pri, WrkQ, Idx, RState>>

\* TODO
IndexerDeleteIndexRecord(i) == 
        /\ IState[i].state = "idx2"
        /\ IState' = [IState EXCEPT ![i] = [state |-> "idx3"]]
        /\ UNCHANGED <<Pri, WrkQ, Idx, RState>>

\* TODO
IndexerUpdateIndexRecord(i) == 
        /\ IState[i].state = "idx3"
        /\ \/ /\ Idx[IState[i].valnew].etag < IState[i].etagnew
              /\ Idx' = [Idx EXCEPT ![IState[i].valnew] = [value |-> IState[i].valnew, etag |-> IState[i].etagnew]]
           \/ /\ Idx' = Idx
        /\ IState' = [IState EXCEPT ![i] = [state |-> "waiting", etagold |-> 0, rvalold |-> ""]] 
        /\ UNCHANGED <<Pri, WrkQ, RState>>
-----------------------------------------------------------------------------
SIdxNext == 
        \/ \E r \in REQUESTS : Process_2_3(r)
        \/ \E r \in REQUESTS : Process_4_5(r)
        \/ \E r \in REQUESTS : Process_6_7(r)
        \/ \E i \in INDEXERS : IndexerRetrieveHint(i)
        \/ \E i \in INDEXERS : IndexerReadPrimaryTable(i)
        \/ \E i \in INDEXERS : IndexerDeleteIndexRecord(i)
        \/ \E i \in INDEXERS : IndexerUpdateIndexRecord(i)
-----------------------------------------------------------------------------
SIdxSpec == SIdxInit /\ [][SIdxNext]_<<vars>>
\* NOTES :
\* Seperation of Indexer locking a record and deleting it later for
\* failure tolerance of an Indexer is not modeled here for simplicity
=============================================================================
