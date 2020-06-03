channel c
abstract ok : message

system A: if True then out(c,ok).

goal True || False.
Proof.
left.
Qed.

goal False || True.
Proof.
right.
Qed.


goal not(forall (t:index), not(cond@A)|| not(cond@A)) => True.
Proof.
nosimpl(intro).
nosimpl(notleft H0).
nosimpl(introsleft H0).
simpl.
Qed.
