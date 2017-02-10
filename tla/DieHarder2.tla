----------------------------- MODULE DieHarder2 -----------------------------

EXTENDS Naturals

CONSTANT buckets,
         capacity,
         goal

ASSUME /\ capacity \in [buckets -> {n \in Nat : n > 0}]
       /\ goal \in Nat
   
Min(m, n) == IF m < n THEN m ELSE n

VARIABLE sizes

TypeOK == /\ sizes \in [buckets -> {n \in Nat : n > 0}]
          /\ \A b \in buckets : sizes[b] \in 0..capacity[b]

\* sizes is a function
\* domain of sizes is buckets
\* provides the function mapping for each item in the domain
Init == sizes = [b \in buckets |-> 0]

FillBucket(i) == /\ sizes' = [sizes EXCEPT ![i] = capacity[i]]

EmptyBucket(i) == /\ sizes' = [sizes EXCEPT ![i] = 0]

PourToBucket(i, j) ==
    LET poured == Min(sizes[i], capacity[j]-sizes[j])
    IN sizes' = [sizes EXCEPT ![i] = @ - poured,
                              ![j] = @ + poured]

Next == \E i \in buckets : \/ EmptyBucket(i)
                           \/ FillBucket(i)
                           \/ \E j \in buckets : PourToBucket(i, j) 

Spec == Init /\ [][Next]_sizes

NotSolved == /\ \A b \in buckets : sizes[b] # goal

Remove(i, seq) ==
    IF i == 0 return Head(seq)
    ELSE Remove(i-1, Tail(seq)
\* capacity <-  (fred :> 3) @@ (mary :> 5)
\* jugs <- [model value] {fred, mary}
\* goal : 4

\* Expression check : 
\* ( Set No Behavoir chevck )
\* [ (fred :> 3) @@ (mary :> 4) EXCEPT ![fred] = 42, ![fred] = 24 ]
=============================================================================
\* Modification History
\* Last modified Wed Feb 08 09:34:10 PST 2017 by sectorzero
\* Created Tue Feb 07 13:17:13 PST 2017 by sectorzero
