channel c

abstract ok:message.

system ((A:out(c,ok))|(B: !_i out(c,ok))).

goal _ (t:timestamp,tau:timestamp): t <= pred(t) => t = init.
Proof.
 auto.
Qed.

goal _ (t:timestamp): t <= pred(A) => t < A.
Proof.
 auto.
Qed.

goal _ (i:index): A <= pred(B(i)) => A < B(i).
Proof.
 auto.
Qed.

goal _: A <> init.
Proof. 
 auto. 
Qed.

goal _: happens (A) => pred(A) <> init.
Proof. 
 checkfail auto exn GoalNotClosed. 
Abort.

set debugConstr=true.
goal _: happens (A) => init < A => pred(A) <> init.
Proof. 
  checkfail auto exn GoalNotClosed.
Abort.

(* True thanks to the property of trace models:
   ∀τ, (happens(τ) ∧ τ ≠ init) ⇒ happens(pred(τ)) *)
goal _ : happens(A) => happens(pred(A)).
Proof.
 by intro Hap.
Qed.

goal _ (i:index): happens(B(i)) => happens(pred(B(i))).
Proof.
 auto.
Qed.
