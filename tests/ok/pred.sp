

system null.

goal _ (t:timestamp): t <= pred(t) => False.
Proof.
 auto.
Qed.

goal _ (t:timestamp): t = pred(t) => not (happens(t)).
Proof.
 auto.
Qed.

(*------------------------------------------------------------------*)
(* if pred(t) happens: then t necessarily does *)
goal _ (t:timestamp): happens(pred(t)) => happens(t).
Proof.
 auto.
Qed.

(* reciprocal does not hold *)
(* if pred(t) happens, then t necessarily does *)
goal _ (t:timestamp): happens(t) => happens(pred(t)).
Proof.
  checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
(* init happens *)
goal _ (t:timestamp): happens(init).
Proof.
 auto.
Qed.

(* happens with two conditions *)
goal _ (t:timestamp): happens(init, init).
Proof.
 auto.
Qed.

(* check that the negation fails *)
goal _ (t:timestamp): not (happens (init)).
Proof.
  checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
(* not true for init *)
goal _ (t:timestamp): happens(t) => pred(t) <= t.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.

(* we can check it *)
goal _ (t:timestamp): t = init => not (happens(pred(t))).
Proof.
 auto.
Qed.

(* or check the contrapositive *)
goal _ (t:timestamp): happens(pred(t)) => t <> init.
Proof.
 auto.
Qed.

(* if we add that t is not init, then it works. *)
goal _ (t:timestamp): happens(t) && t <> init => pred(t) <= t.
Proof.
 auto.
Qed.

(* we check that the condition that t happens is necessary *)
goal _ (t:timestamp): t <> init => pred(t) <= t.
Proof.
  checkfail auto exn GoalNotClosed.
Abort.

(*------------------------------------------------------------------*)
goal _ (t,t':timestamp): t <= t' => happens(t, t').
Proof.
  auto.
Qed.

goal _ (t,t':timestamp): t < t'  => happens(t,t').
Proof.
  auto.
Qed.

goal _ (t,t':timestamp): t > t'  => happens(t,t').
Proof.
  auto.
Qed.

goal _ (t,t':timestamp): t >= t' => happens(t,t').
Proof.
  auto.
Qed.
