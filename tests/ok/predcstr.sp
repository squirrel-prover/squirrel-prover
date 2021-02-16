set autoIntro=false.

channel c
abstract ok:message
system ((A:out(c,ok))|(B: !_i out(c,ok))).

goal _ (t:timestamp,tau:timestamp): t <= pred(t) => t = init.
Proof.
 by auto.
Qed.

goal _ (t:timestamp): t <= pred(A) => t < A.
Proof.
 by auto.
Qed.

goal _ (i:index): A <= pred(B(i)) => A < B(i).
Proof.
 by auto.
Qed.

goal _: A <> init.
Proof. 
 by auto. 
Qed.

goal _: happens (A) => pred(A) <> init.
Proof. 
 checkfail auto exn GoalNotClosed. 
Abort.

goal _ : happens(A) => happens(pred(A)).
Proof.
 intro Hap.
 by auto.
Qed.

goal _ (i:index): happens(B(i)) => happens(pred(B(i))).
Proof.
 by auto.
Qed.
