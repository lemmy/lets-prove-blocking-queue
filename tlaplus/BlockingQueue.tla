-------------------- MODULE BlockingQueue -----------------------
EXTENDS Naturals, Sequences, TLAPS

CONSTANTS Producers, Consumers, BufCapacity

ASSUME Assumptions == /\ Producers # {} /\ Consumers # {}
                      /\ (Consumers \intersect Producers) = {}
                      /\ BufCapacity \in (Nat \ {0})

data == CHOOSE d : d \* Some data.

-----------------------------------------------------------------

VARIABLES buffer, waitC, waitP
vars == <<buffer, waitC, waitP>>

TypeOK == /\ Len(buffer) \in 0..BufCapacity
          /\ waitP \in SUBSET Producers
          /\ waitC \in SUBSET Consumers

NoDeadlock == (waitC \cup waitP) # (Producers \cup Consumers)

Notify(ws) == IF ws # {}
              THEN \E x \in ws: ws' = ws \ {x}
              ELSE UNCHANGED ws

Wait(ws, t) == /\ ws' = ws \cup {t}
               /\ UNCHANGED buffer

Put(t, d) == \/ /\ Len(buffer) < BufCapacity
                /\ buffer' = Append(buffer, d)
                /\ Notify(waitC) /\ UNCHANGED waitP
             \/ /\ Len(buffer) = BufCapacity
                /\ Wait(waitP, t) /\ UNCHANGED waitC
      
Get(t) == \/ /\ buffer # <<>>
             /\ buffer' = Tail(buffer)
             /\ Notify(waitP) /\ UNCHANGED waitC
          \/ /\ buffer = <<>>
             /\ Wait(waitC, t) /\ UNCHANGED waitP

Init == buffer = <<>> /\ waitC = {} /\ waitP = {}

Next == \/ \E t \in (Producers \ waitP): Put(t, data)
        \/ \E t \in (Consumers \ waitC): Get(t)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------

(* Scaffolding: Establish that TypeOK is inductive. *)
LEMMA ITypeInv == Spec => []TypeOK
<1> USE Assumptions DEF TypeOK
<1>1. Init => TypeOK 
   BY DEF Init
<1>2. TypeOK /\ [Next]_vars => TypeOK'  
  BY DEF Next, vars, Put, Get, Notify, Wait
<1>. QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------

(* An inductive invariant that implies NoDeadlock. *)
IInv == /\ TypeOK
        /\ NoDeadlock
        (* This is the meat! *)
        /\ buffer = <<>> => (Producers \ waitP) # {}
        /\ Len(buffer) = BufCapacity => (Consumers \ waitC) # {}

-----------------------------------------------------------------

(* Proof that Spec is deadlock-free. *)
THEOREM DeadlockFreedom == Spec => []IInv
<1> USE Assumptions DEF IInv, NoDeadlock, TypeOK
<1>1. Init => IInv
  BY DEF Init
<1>2. IInv /\ [Next]_vars => IInv' 
  BY DEF Next, vars, Put, Get, Notify, Wait
<1>3. IInv => NoDeadlock
  BY DEF IInv
<1>4. QED
  BY <1>1,<1>2,<1>3,PTL DEF Spec
  
=================================================================
