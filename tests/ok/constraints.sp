system null.

(*------------------------------------------------------------------*)
lemma _ (i:index): i = i.
Proof.
  constraints.
Qed.

abstract I : index.

lemma _ : I = I.
Proof.
  constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ : I <> I.
Proof.
  checkfail constraints exn Failure.
Abort.

(*------------------------------------------------------------------*)
lemma _ (t:timestamp): t = t.
Proof.
 constraints.
Qed.

abstract T : timestamp.

lemma _ : T = T.
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (i:index,j:index): i=j => j=i.
Proof.
 constraints.
Qed.

abstract J : index.

lemma _: I=J => J=I.
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (i:index,j:index): i=j => not(j<>i).
Proof.
 constraints.
Qed.

lemma _ : I=J => not(J<>I).
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x:timestamp,y:timestamp): x=y => y=x.
Proof.
 constraints.
Qed.

abstract X : timestamp.
abstract Y : timestamp.

lemma _ : X=Y => Y=X.
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x:timestamp,y:timestamp): x<>y => y<>x.
Proof.
  constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x:timestamp,y:timestamp,z:timestamp):
  x=y => y=z => x<>z => false.
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x:timestamp,y:timestamp,z:timestamp):
  y=z => x<>z => x<>y.
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
lemma _ (x:timestamp,y:timestamp,z:timestamp):
  y=z => x<>z => not(x=y).
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
axiom eq_iff (x, y : boolean) : (x = y) = (x <=> y).

lemma _ (t, t' : timestamp): (t <= pred(t')) = (t < t').
Proof. 
  by rewrite eq_iff. 
Qed.

(*------------------------------------------------------------------*)
(* `pred(init)` does not happens *)
lemma _ : not (happens(pred(init))).
Proof. constraints. Qed.

(*------------------------------------------------------------------*)
(* surprisingly, if `pred(tau)` happens, then so does `tau` since
   `pred(_)` sends non-happening timestamps to non-happening 
   timestamps. *)
lemma _ (tau : timestamp) : happens(pred(tau)) => happens(tau).
Proof. constraints. Qed.

lemma _ : happens(pred(X)) => happens(X).
Proof. constraints. Qed.

(*------------------------------------------------------------------*)
lemma _ (t:timestamp): t < init => t = init.
Proof.
 constraints.
Qed.

lemma _: T < init => T = init.
Proof.
 constraints.
Qed.

(*------------------------------------------------------------------*)
(* check that global sequents know how to exploits unsatisfiable 
   constraints in reachability hypotheses. *)
global lemma _ (t:timestamp, x,y:message):
   [t < init] -> [t <> init] -> equiv (diff(x,y)).
Proof.
 intro H H1. 
 constraints. 
Qed.

global lemma _ (x,y:message):
   [T < init] -> [T <> init] -> equiv (diff(x,y)).
Proof.
 intro H H1. 
 constraints. 
Qed.
