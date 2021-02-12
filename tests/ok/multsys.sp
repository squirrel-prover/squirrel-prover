set autoIntro=false.

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

expandall.
fa 0; fa 1. 
noif 1. 
by auto.

expandall.
fa 0.
Qed.

equiv [left,toto] [right,toto] test2.
Proof.
induction t.

expandall.
fa 0; fa 1. 
noif 1.
by auto.

expandall.
by fa 0.
Qed.
