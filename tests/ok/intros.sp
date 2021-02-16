set autoIntro=false.

channel c
abstract ok : message

system A: if True then out(c,ok).

goal _: True || False.
Proof.
left.
Qed.

goal _: False || True.
Proof.
right.
Qed.


goal _: not(forall (t:index), not(cond@A)|| not(cond@A)) => True.
Proof.
nosimpl(intro H).
nosimpl(notleft H).
nosimpl(destruct H).
simpl.
Qed.

goal _: not(forall (t:index), not(cond@A)|| not(cond@A)) => True.
Proof.
nosimpl(intro H).
nosimpl(notleft H).
nosimpl(destruct H as [t [Hc Hc2]]). 
auto.
Qed.
