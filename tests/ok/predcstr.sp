channel c
abstract ok:message
system ((A:out(c,ok))|(B: !_i out(c,ok))).

goal forall (t:timestamp,tau:timestamp), t <= pred(t) => t = init.
Proof.
 simpl.
Qed.

goal forall (t:timestamp), t <= pred(A) => t < A.
Proof.
 simpl.
Qed.

goal forall (i:index), A <= pred(B(i)) => A < B(i).
Proof.
 simpl.
Qed.
