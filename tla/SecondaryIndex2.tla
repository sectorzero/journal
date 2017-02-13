--------------------------------- MODULE SecondaryIndex2 ---------------------------------
(***************************************************************************)
(* This module specifies a protocol for updating a secondary-index with    *)
(* eventual consistency semantics with the the index guranteed to be       *)
(* updated with the highest-known-snapshot of the version of the key       *)
(* in the primary table                                                    *)
(*                                                                         *)
(* This specification defines the protocol for the update of values of     *)
(* a single key K                                                          *)
(*                                                                         *)
(*                                                                         *)
(* We specify only safety properties, not liveness properties.             *) 
(* We simplify the specification in the following ways.                    *)
(*                                                                         *)
(***************************************************************************)
\* To add in description
\* Single key example
\* Delete simplificationa and equivalence
\* k1..kN -> V simplification & equivalence using V == V,kX as the secondary-key
\* Simplification <PK,RK> -> K
\* Key Correctness : <K:K,Value:V,ETag:e> -> <Key:<Value,Key>, Etag:e>
EXTENDS Integers, Sequences

\* Remove(i, seq) == 
\*   [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] ELSE seq[j+1]]

Last(seq) == 
  IF Len(seq) = 0 THEN {} ELSE seq[Len(seq)]

\*RemoveLast(seq) == 
\*  IF Len(seq) = 0 THEN seq ELSE SubSeq(seq, 1, Len(seq)-1)

-----------------------------------------------------------------------------
CONSTANT 
    REQUESTS, 
    INDEXERS
-----------------------------------------------------------------------------
VARIABLES 
    Pri,          \* Primary Table Log Of Updates For A Single Key,
    Idx,          \* Idx Table Log of Index Record Updates,
    RState,       \* RState[r] Requests State
    IState        \* IState[i] Indexers State
    WrkQ,         \* Updates Hint Set,

vars == <<Pri, Idx, RState, IState, WrkQ>>

\* Records ( PrimaryKey implied as spec is for a single PrimaryKey )
\* Primary : [type:"primary", value:"somevalue", etag:3]
\* Index   : [type:"index", key:"somevalue", etag:3]
UpdateRecords == 
    [t: {"primary"}, 
     v: {"initial"} \cup {allstrings}, 
     e: {x \in Int : x > 0}]

\* IndexRecords ==
\*     [t: {"index"}, 
\*      k: {"initial"} \cup {allstrings}, 
\*      e: {x \in Int : x > 0}, 
\*      s: {"active", "deleted"}]

IndexRecordsT ==
    [t: {"index"}, 
     k: {"initial"} \cup {allstrings}, 
     e: {x \in Int : x >= 0}, 
     s: {"notseen", "active", "deleted"}]

RequestMessages ==
    [v: {allstring} \ {"initial"}, 
     s: {"unprocessed", "read", "queued", "updated"}
     r: {UpdateRecords}]

\* Immutable
IndexerMessage ==
    [v: {allstring} \ {"initial"}, 
     o: {UpdateRecords}]

IndexerStateData ==
    [s: {"waiting", "picked", "do_update_1", "do_update_2"},
     m: {IndexerMessage},
     n: {UpdateRecords}]

InitialUpdateRecord == 
    [t |-> "primary", v |-> "initial", e |-> 1]

EmptyUpdateRecord == 
    [t |-> "primary", v |-> "", e |-> 0]

InitialIndexRecord == 
    [t |-> "index", k |-> "initial", e |-> 1]

IndexerStateReset == [ s |-> "waiting", 
                       m |-> [v |-> "", o |-> EmptyUpdateRecord],
                       n |-> EmptyUpdateRecord ]
                        
Init == /\ Pri = << InitialUpdateRecord >>
        /\ Idx = [m \in REQUESTS \cup {"initial"} |->
            [t |-> "index", k |-> m, e |-> 0, s: "notseen"]
        \* /\ Idx = << InitialIndexRecord >>
        /\ WrkQ = {} 
        /\ RState = [m \in REQUESTS |-> 
            [v |-> m, s |-> "unprocessed", r |-> EmptyUpdateRecord]] 
        /\ IState = [i \in INDEXERS |-> IndexerStateReset ]
-----------------------------------------------------------------------------
(***************************************************************************)
(*                          UpdateRequest ACTIONS                          *)
(***************************************************************************)
UpdateReq_ReadLatestValFromPrimary(m) ==
  (*************************************************************************)
  (* Phase 1 of the Update Request : Reads the current value of K from the *)
  (* primary table. ( 2,3 in Fig )                                         *)
  (*************************************************************************)
  /\ RState[m].s = "unprocessed"
  /\ LET currval == Last(Pri)
     IN /\ RState' = [RState EXCEPT ![m] = 
            [v |-> @.v, s |-> "read", r |-> currval]]
  /\ UNCHANGED <<Pri, Idx, IState, WrkQ>>

UpdateReq_AddOptimisticUpdateHintMessage(m) == 
  (*************************************************************************)
  (* Phase 1 of the Update Request : Enqueues the read value as an optimis *)
  (* tic hint or marker for the updater to work on. ( 4,5 in Fig )         *)
  (*************************************************************************)
  /\ RState[m].s = "read"
  /\ WrkQ' = WrkQ \cup { [v |-> RState[m].v, o |-> RState[m].r] }
  /\ RState' = [RState EXCEPT ![m] = 
            [v |-> @.v, s |-> "queued", r |-> @.r]]
  /\ UNCHANGED <<Pri, Idx, IState>>

UpdateReq_UpdateValueInPrimary(m) ==
  (*************************************************************************)
  (* Phase 3 of the Update Request : Updates the new value of K in  the    *)
  (* primary table. ( 6,7 in Fig )                                         *)
  (*************************************************************************)
  /\ RState[m].s = "queued"
  /\ LET latestvalue == Last(Pri)
     IN /\ Pri' = 
            Append(Pri, [t |-> "primary", v |-> m, e |-> latestvalue.e + 1])
        /\ RState' = [RState EXCEPT ![m] = 
            [v |-> @.v, s |-> "updated", r |-> @.rval]]
  /\ UNCHANGED <<Idx, IState, WrkQ>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          Indexer ACTIONS                                *)
(***************************************************************************)
Indexer_PickMessage(i, m) == 
  (*************************************************************************)
  (* Dequeues an update-hint to propate the change in K for. This record   *)
  (* was added optimistically                                              *)
  (*************************************************************************)
  /\ IState[i].s = "waiting"
  /\ IState' = [IState EXCEPT ![i] = 
            [s |-> "picked", o |-> m, n |-> @.valnew]]
  /\ UNCHANGED <<Pri, Idx, RState, WrkQ>>

Indexer_ReadLatestValueFromPrimary(i) ==
  (*************************************************************************)
  (* Indexer reads the latest value of the PK ad determines if it has moved*)
  (* forward in version. If so it will continue the update process for the *)
  (* index else ignores the update hint. Note the idempotency              *)
  (*************************************************************************)
  /\ IState[i].s = "picked"
  /\ LET latestvalue == Last(Pri)
     IN /\ IF IState[i].o.e < latestvalue.e
           THEN /\ IState' = [IState EXCEPT ![i] = 
                    [s |-> "do_update_1", o |-> @.o, n |-> latestvalue]]
           ELSE
                /\ IState' = [IState EXCEPT ![i] = IndexerStateReset]           
  /\ UNCHANGED <<Pri, Idx, RState, WrkQ>>

\* Indexer_DeleteOldValueFromIndex(i) == 
\*   (*************************************************************************)
\*   (* Tries to delete 'an' old value from the Index                         *)
\*   (*************************************************************************)
\*   /\ IState[i].s = "do_update_1"
\*   /\ LET oldvalue == IState[i].o
\*          idxvalue == 
\*             CHOOSE j \in Idx : /\ j.v = oldvalue.v
\*                                /\ j.e = oldvalue.e 
\*                                \* note EQ is a stronger check than LTE 
\*                                \* we can relax this to LTE if needed
\*      IN IF idxvalue # {}
\*         THEN /\ Idx' = {r \in Idx : /\ r.v # oldvalue.v
\*                                     /\ r.e # oldvalue.e}
\*                         \cup
\*                        {[j EXCEPT !.s = "deleted"]} 
\*              /\ IState' = [IState EXCEPT ![i] =
\*                         [s |-> "do_update_2", o |-> @.o, n |-> @.n]]
\*         ELSE /\ Idx' = Idx 
\*              /\ IState' = [IState EXCEPT ![i] = IndexerStateReset ]
\*   /\ UNCHANGED <<Pri, WrkQ, Idx, RState>>

Indexer_DeleteOldValueFromIndex(i) == 
  (*************************************************************************)
  (* Tries to delete 'an' old value from the Index                         *)
  (*************************************************************************)
  /\ IState[i].s = "do_update_1"
  /\ LET oldvalue == IState[i].o
         idxvalue == IdxT[oldvalue.v]
     IN IF /\ idxvalue.e = oldvalue.e 
        THEN /\ IdxT' = [IdxT EXCEPT ![idxvalue.k] =  
                    [k |-> @.k, 
                     e |-> oldvalve.e, 
                     s |-> "deleted", 
                     t |-> @.t]]
             /\ IState' = [IState EXCEPT ![i] =
                        [s |-> "do_update_2", o |-> @.o, n |-> @.n]]
        ELSE /\ IdxT' = IdxT 
             /\ IState' = [IState EXCEPT ![i] = IndexerStateReset ]
  /\ UNCHANGED <<Pri, WrkQ, Idx, RState>>

\* Indexer_UpdateIndexWithLatestValue(i) == 
\*   (*************************************************************************)
\*   (* Insert or Update the latest known snapshot version of the PK ensuring *)
\*   (* an monotonic update in version. Note the idempotency                  *)
\*   (*************************************************************************)
\*   /\ IState[i].s = "do_update_2"
\*   /\ LET latestidxval == 
\*             CHOOSE j \in Idx : j.s = "active"
\*      IN IF \/ latestidxval = {}
\*            \/ /\ latestidxval # {}
\*               /\ latestidxval.e < IState[i].n.e
\*         THEN Idx' = Append(Idx, 
\*                     [t |-> "index", 
\*                      k |-> IState.n.v, 
\*                      e |-> IState.n.e, 
\*                      s |-> "active"])
\*         ELSE Idx' = Idx
\*   /\ IState' = [IState EXCEPT ![i] = IndexerResetRecord]          
\*   /\ UNCHANGED <<Pri, RState, WrkQ>>

Indexer_UpdateNewValueInIndex(i) == 
  (*************************************************************************)
  (* Insert or Update the latest known snapshot version of the PK ensuring *)
  (* an monotonic update in version. Note the idempotency                  *)
  (*************************************************************************)
  /\ IState[i].s = "do_update_2"
  /\ LET newval = IState[i].n 
         indexval == IdxT[newval.v] 
     IN IF indexval.e < newval.e
        THEN IdxT' = [IdxT EXCEPT [indexval.k] = 
                        [k |-> @.k, 
                         e |-> newval.e
                         s |-> "active", 
                         t |-> @.t]]
        ELSE IdxT' = Idx
  /\ IState' = [IState EXCEPT ![i] = IndexerStateReset]          
  /\ UNCHANGED <<Pri, RState, WrkQ>>
-----------------------------------------------------------------------------
SIdxNext == 
  \/ \E r \in REQUESTS : UpdateReq_ReadLatestValueFromPrimary(r)
  \/ \E r \in REQUESTS : UpdateReq_AddOptimisticUpdateHintMessage(r)
  \/ \E r \in REQUESTS : UpdateReq_UpdateValueInPrimary(r)
  \/ \E i \in INDEXERS : Indexer_PickMessage(i)
  \/ \E i \in INDEXERS : Indexer_ReadLatestValueFromPrimary(i)
  \/ \E i \in INDEXERS : Indexer_DeleteOldValueFromIndex(i)
  \/ \E i \in INDEXERS : Indexer_UpdateNewValueInIndex(i)
-----------------------------------------------------------------------------
SIdxSpec == SIdxInit /\ [][SIdxNext]_<<vars>>
-----------------------------------------------------------------------------
\* Safety Invariants
\* The specification of the inconsistent index update protocol expects that the
\* sequential log of changes applied to the primary and index table are always
\* valid. ( check for monotonic sequential consistency ) 
\* /\ a. An index update record should be due to a valid primary key update
\* /\ b. Only one active index update record is present ( all others are deleted )
\* /\ c. The etag of active index update record is GT all other other previous
\*       index update records ( Note: there can be no active records at any
\*       time as there is a gap between delete and insert of the index record )
-----------------------------------------------------------------------------
\* Fairness Invariants
\* The specification of inconsistent index update protocol expects that the last
\* update to the primary key is eventually applied on the index. For the spec
\* of this protocol, it does not matter if intermediate updates are missed
\* but we need to guarantee that the last update is always applied at some
\* time eventually
-----------------------------------------------------------------------------
\* NOTES :
\* Seperation of Indexer locking a record and deleting it later for
\* failure tolerance of an Indexer is not modeled here for simplicity
=============================================================================
