

include Basic.

abstract ok : message
abstract ko : message

abstract koo : message

abstract f : message->message

mutable S : message = empty

name n : message
name m : message
name k : message

hash h

channel c

system [t1] !_i if diff(True,False)  then (S:= diff(ok,koo); out(c,diff(S,ko))).

system [t2] !_i if diff(False,ok=ok) then (S:= diff(koo,ok); out(c,diff(ko,S))).


equiv [t1/left, t2/right] test.
Proof.
induction t.
auto. 

nosimpl(expandall).
fa 0. fa 1.
auto. 

nosimpl(expandall).
fa 0; fa 1.
auto.
Qed.
