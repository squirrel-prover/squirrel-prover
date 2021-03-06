set autoIntro=false.

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


equiv [left,t1] [right,t2] test.
Proof.
induction t.
nosimpl(expandall).
fa 0. fa 1.
equivalent ok=ok, True.
by auto.
nosimpl(expandall).
fa 0; fa 1.
equivalent ok=ok, True.
by auto.
Qed.
