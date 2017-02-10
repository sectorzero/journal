--------------------------------- MODULE SecondaryIndex ---------------------------------
(***************************************************************************)
(* This module specifies a protocol for updating a secondary-index with    *)
(* eventual consistency semantics with the the index guranteed to be       *)
(* updated with the highest-known-snapshot of the version of the key       *)
(* in the primary table                                                    *)
(*                                                                         *)
(* This specification defines the protocol for the update of values of     *)
(* a single key K                                                          *)
(*                                                                         *)
(* We specify only safety properties, not liveness properties.             *) 
(* We simplify the specification in the following ways.                    *)
(*                                                                         *)
(***************************************************************************)
EXTENDS Integers, Sequences

Remove(i, seq) == 
    [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Last(seq) == 
    IF Len(seq) = 0 THEN {} ELSE seq[Len(seq)]

RemoveLast(seq) == 
    IF Len(seq) = 0 THEN seq ELSE SubSeq(seq, 1, Len(seq)-1)

-----------------------------------------------------------------------------
CONSTANT REQUESTS, INDEXERS
-----------------------------------------------------------------------------
VARIABLES Pri,          \* Primary Table Log Of Updates For A Single Key,
          WrkQ,         \* Updates Hint Queue,
          Idx,          \* Idx[Value] Index Table,
          RState,       \* RState[r] Requests State
          IState        \* IState[i] Indexers State

vars == <<Pri, WrkQ, Idx, RState, IState>>

EmptyRecord == [etag |-> 0, val |-> ""]

InitialRecord == [etag |-> 1, val |-> "initial"]

IndexerResetRecord == [ state |-> "waiting", 
                        valold |-> EmptyRecord,
                        valnew |-> EmptyRecord ]
                        
SIdxInit == /\ Pri = << InitialRecord >>
            /\ WrkQ = << >>
            /\ Idx = [v \in { InitialRecord.val } |-> InitialRecord.etag]
            /\ RState = [r \in REQUESTS |-> [state |-> "unprocessed", rval |-> EmptyRecord]] 
            /\ IState = [i \in INDEXERS |-> IndexerResetRecord ]
-----------------------------------------------------------------------------
(***************************************************************************)
(*                          UpdateRequest ACTIONS                          *)
(***************************************************************************)
UpdateReq_ReadCurrValueFromPrimaryTable(r) ==
  (*************************************************************************)
  (* Phase 1 of the Update Request : Reads the current value of K from the *)
  (* primary table. ( 2,3 in Fig )                                         *)
  (*************************************************************************)
  /\ RState[r].state = "unprocessed"
  /\ LET currval == Last(Pri)
     IN /\ RState' = [RState EXCEPT ![r] = 
            [state |-> "readvalue", rval |-> currval]]
  /\ UNCHANGED <<Pri, WrkQ, Idx, IState>>

UpdateReq_EnqueueOptimisticUpdateHint(r) == 
  (*************************************************************************)
  (* Phase 1 of the Update Request : Enqueues the read value as an optimis *)
  (* tic hint or marker for the updater to work on. ( 4,5 in Fig )         *)
  (*************************************************************************)
  /\ RState[r].state = "readvalue"
  /\ WrkQ' = Append(WrkQ, RState[r].rval)
  /\ RState' = [RState EXCEPT ![r] = [state |-> "queued", rval |-> @.rval]]
  /\ UNCHANGED <<Pri, Idx, IState>>

UpdateReq_NewValueInPrimaryTable(r) ==
  (*************************************************************************)
  (* Phase 3 of the Update Request : Updates the new value of K in  the    *)
  (* primary table. ( 6,7 in Fig )                                         *)
  (*************************************************************************)
  /\ RState[r].state = "queued"
  /\ LET latestvalue == Last(Pri)
     IN /\ Pri' = Append(Pri, [etag |-> latestvalue.etag + 1, val |-> r])
        /\ RState' = [RState EXCEPT ![r] = [state |-> "updated", rval |-> @.rval]]
  /\ UNCHANGED <<WrkQ, Idx, IState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          Indexer ACTIONS                                *)
(***************************************************************************)
Indexer_DequeueOptimisticUpdateHint(i) == 
  (*************************************************************************)
  (* Dequeues an update-hint to propate the change in K for. This record   *)
  (* was added optimistically                                              *)
  (*************************************************************************)
  /\ IState[i].state = "waiting"
  /\ Len(WrkQ) > 0
  /\ LET updatehint == Head(WrkQ)
     IN /\ IState' = [IState EXCEPT ![i] = 
            [state |-> "idx_dequeued", valold |-> updatehint, valnew |-> @.valnew]]
        /\ WrkQ' = Tail(WrkQ)
  /\ UNCHANGED <<Pri, Idx, RState>>

Indexer_ReadLatestValueFromPrimaryTable(i) ==
  (*************************************************************************)
  (* Indexer reads the latest value of the PK ad determines if it has moved*)
  (* forward in version. If so it will continue the update process for the *)
  (* index else ignores the update hint. Note the idempotency              *)
  (*************************************************************************)
  /\ IState[i].state = "idx_dequeued"
  /\ LET latestvalue == Last(Pri)
     IN \/ /\ IState[i].valold.etag < latestvalue.etag
           /\ IState' = [IState EXCEPT ![i] = 
                [state |-> "idx_do_update_1", valold |-> @.valold, valnew |-> latestvalue]]
        \/ /\ IState' = [IState EXCEPT ![i] = IndexerResetRecord]           
  /\ UNCHANGED <<Pri, WrkQ, Idx, RState>>

Indexer_DeleteOldValueFromIndex(i) == 
  (*************************************************************************)
  (* Tries to delete the old value from the Index                          *)
  (*************************************************************************)
  /\ IState[i].state = "idx_do_update_1"
  /\ LET oldkey == IState[i].valold.val
     IN /\ Idx' = Idx \ oldkey
  /\ IState' = [IState EXCEPT ![i] = [state |-> "idx_do_update_2"]]
  /\ UNCHANGED <<Pri, WrkQ, Idx, RState>>

Indexer_UpdateIndexWithLatestValue(i) == 
  (*************************************************************************)
  (* Insert or Update the latest known snapshot version of the PK ensuring *)
  (* an monotonic update in version. Note the idempotency                  *)
  (*************************************************************************)
  /\ IState[i].state = "idx_do_update_2"
  /\ LET latestindexvalue == Idx[IState[i].valnew.val]
     IN \/ /\ latestindexvalue = {}
           /\ Idx' = [Idx EXCEPT ![IState[i].valnew.val] = 
                [etag |-> IState[i].valnew.etag]]
        \/ /\ latestindexvalue.etag < IState[i].valnew.etag
           /\ Idx' = [Idx EXCEPT ![IState[i].valnew.val] = 
                [etag |-> IState[i].valnew.etag]]
        \/ /\ Idx' = Idx
  /\ IState' = [IState EXCEPT ![i] = IndexerResetRecord]          
  /\ UNCHANGED <<Pri, WrkQ, RState>>
-----------------------------------------------------------------------------
SIdxNext == 
  \/ \E r \in REQUESTS : UpdateReq_ReadCurrValueFromPrimaryTable(r)
  \/ \E r \in REQUESTS : UpdateReq_EnqueueOptimisticUpdateHint(r)
  \/ \E r \in REQUESTS : UpdateReq_NewValueInPrimaryTable(r)
  \/ \E i \in INDEXERS : Indexer_DequeueOptimisticUpdateHint(i)
  \/ \E i \in INDEXERS : Indexer_ReadLatestValueFromPrimaryTable(i)
  \/ \E i \in INDEXERS : Indexer_DeleteOldValueFromIndex(i)
  \/ \E i \in INDEXERS : Indexer_UpdateIndexWithLatestValue(i)
-----------------------------------------------------------------------------
SIdxSpec == SIdxInit /\ [][SIdxNext]_<<vars>>
\* NOTES :
\* Seperation of Indexer locking a record and deleting it later for
\* failure tolerance of an Indexer is not modeled here for simplicity
=============================================================================
