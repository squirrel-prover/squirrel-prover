channel c

abstract ok:message
abstract ko:message

system in(c,x); if x=ok then out(c,diff(x,ok)).

equiv test.
Proof.
induction t.
expandall.
fa 0.
fa 1.
nosimpl(ifeq 1,input@A,ok).
simpl.
nosimpl(fadup).
assumption.

expandall.
fa 0.
Qed.
