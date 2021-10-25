set autoIntro=false.

channel c

abstract ok:message
abstract ko:message

system in(c,x); if x=ok then out(c,diff(x,ok)).

equiv test.
Proof.
induction t.

auto. 

expand frame, output, exec, cond.
fa 0; fa 1.
nosimpl(ifeq 1,input@A,ok). 
auto.

nosimpl(fadup).
assumption.

expandall.
by fa 0.
Qed.
