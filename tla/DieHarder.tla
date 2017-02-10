------------------------------ MODULE DieHarder ----------------------------- 
EXTENDS Integers

CONSTANTS SIZES, G

VARIABLE jugs
-----------------------------------------------------------------------------
DHTypeOK ==
    \A i \in 1..Len(SIZES) : jugs[i] \in 0..SIZES[i]

Init == jugs = [i \in 1..Len(SIZES) |-> 0]   

FillJug(i)  == /\ jugs' = [jugs EXCEPT ![i] = SIZES[i]]

EmptyJug(i) == /\ jugs' = [jugs EXCEPT ![i] = 0]

Min(m, n) == IF m < n THEN m ELSE n
Abs(x) == IF x < 0 THEN -x ELSE x

PourIntoJug(i, j) ==
    LET poured == Abs(Min(i + j, SIZES[j]) - j)
    IN /\ jugs' = [jugs EXCEPT ![i] = i - poured, ![j] = j + poured]

Next == \/ \E i \in 1..Len(SIZES) : FillJug(i) \/ EmptyJug(i)
        \/ \E i, j \in 1..Len(SIZES) : /\ i # j 
                                       /\ PourIntoJug(i, j)   
=============================================================================
