system null.

lemma _ (t:timestamp): t <= pred(t) => False.
Proof.
 constraints.
Qed.

lemma _ (t:timestamp): t = pred(t) => not (happens(t)).
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
(* if pred(t) happens: then t necessarily does *)
lemma _ (t:timestamp): happens(pred(t)) => happens(t).
Proof.
 constraints.
Qed.

(* reciprocal does not hold *)
(* if pred(t) happens, then t necessarily does *)
lemma _ (t:timestamp): happens(t) => happens(pred(t)).
Proof.
  checkfail constraints exn Failure. (* constraints satisfiable *)
Abort.

(*------------------------------------------------------------------*)
(* init happens *)
lemma _ : happens(init).
Proof.
 constraints.
Qed.

(* happens with two conditions *)
lemma _ : happens(init, init).
Proof.
 constraints.
Qed.

(* check that the negation fails *)
lemma _ : not (happens (init)).
Proof.
  checkfail constraints exn Failure. (* constraints satisfiable *)
Abort.

(* `pred init` does not happens *)
lemma _ : not (happens (pred init)).
Proof.
  constraints.
Qed.

(*------------------------------------------------------------------*)
(* not true for init *)
lemma _ (t:timestamp): happens(t) => pred(t) <= t.
Proof.
  checkfail constraints exn Failure. (* constraints satisfiable *)
Abort.

(* we can check it *)
lemma _ (t:timestamp): t = init => not (happens(pred(t))).
Proof.
 constraints.
Qed.

(* or check the contrapositive *)
lemma _ (t:timestamp): happens(pred(t)) => t <> init.
Proof.
 constraints.
Qed.

(* if we add that t is not init, then it works. *)
lemma _ (t:timestamp): happens(t) && t <> init => pred(t) <= t.
Proof.
 constraints.
Qed.

(* we check that the condition that t happens is necessary *)
lemma _ (t:timestamp): t <> init => pred(t) <= t.
Proof.
  checkfail constraints exn Failure. (* constraints satisfiable *)
Abort.

(*------------------------------------------------------------------*)
lemma _ (t:timestamp): happens(pred t) => pred t <= t.
Proof. 
  constraints. 
Qed.

lemma _ (t:timestamp): 
  happens(pred (pred t)) => 
  (pred (pred t) <= pred t && pred (pred t) <= t).
Proof. 
  constraints. 
Qed.

lemma _ (t:timestamp): 
  happens(pred (pred (pred t))) => 
  (pred (pred (pred t)) <= pred (pred t) && 
   pred (pred (pred t)) <= pred t && 
   pred (pred (pred t)) <= t).
Proof. 
  constraints. 
Qed.

(*------------------------------------------------------------------*)
lemma _ (t,t':timestamp): t <= t' => happens(t, t').
Proof.
  constraints.
Qed.

lemma _ (t,t':timestamp): t < t'  => happens(t,t').
Proof.
  constraints.
Qed.

lemma _ (t,t':timestamp): t > t'  => happens(t,t').
Proof.
  constraints.
Qed.

lemma _ (t,t':timestamp): t >= t' => happens(t,t').
Proof.
  constraints.
Qed.

(*------------------------------------------------------------------*)
lemma [any] _ (t,t':timestamp) :
  pred t <= t' =>
  not (pred t = t') =>
  not (t <= t') =>
  false.
Proof.
  intro *.
  constraints.
Qed.

lemma [any] _ (t,t':timestamp) :
  pred (pred t) <= t' =>
  not (pred (pred t) = t') =>
  not (pred t = t') =>
  not (t <= t') =>
  false.
Proof.
  intro *.
  constraints.
Qed.

lemma [any] _ (t,t':timestamp) :
  pred (pred (pred t)) <= t' =>
  not (pred (pred (pred t)) = t') =>
  not (pred (pred t) = t') =>
  not (pred t = t') =>
  not (t <= t') =>
  false.
Proof.
  intro *.
  constraints. 
Qed.
