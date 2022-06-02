

include Basic.

name ok : message
name ko : message
name koo : message

channel c

process A(res:message) =  if False then out(c,res)

system !_i A(diff(ok,ko)).

system [toto] !_i A(diff(ko,koo)).

equiv test.
Proof.
induction t.

auto. 

expandall.
fa 0; fa 1. 
by rewrite if_false in 1. 

expandall.
by fa 0.
Qed.

equiv [toto] test2.
Proof.
induction t.

auto.

expandall.
fa 0; fa 1. 
by rewrite if_false in 1.

expandall.
by fa 0.
Qed.
