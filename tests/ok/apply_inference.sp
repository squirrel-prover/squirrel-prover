(* test apply argument inference *)


system null.

abstract nt ['a] : 'a -> 'a.
abstract ft ['a] : 'a * 'a -> 'a.
abstract gt ['a] : 'a * 'a -> bool.

goal _ (x, y : message) : 
    (forall (z : message), gt(nt(x),z) => false) => 
    gt(nt(x),nt(y)) => 
    false.
Proof.
  intro H A.
  by have G := H _ A.
Qed.

(* same with a type variable *)
goal _ ['a] (x, y : 'a) : 
    (forall (z : 'a), gt(nt(x),z) => false) => 
    gt(nt(x),nt(y)) => 
    false.
Proof.
  intro H A.
  by have G := H _ A.
Qed.

goal _ ['a] (x, y : 'a) : 
    (forall (z : 'a), gt(nt(x),z) => false) => 
    gt(nt(y),nt(y)) => 
    false.
Proof.
  intro H A. 
  checkfail by try have G := H _ A exn GoalNotClosed.
Abort.


abstract P : message -> boolean.
abstract Q : message -> boolean.
abstract (++) : message -> message -> message.

goal _ (y : message) :
  (forall (x : message), P (x) => Q (x)) =>
  (P(y ++ zero)) =>
  Q (y ++ zero).
Proof.
  intro H G.
  apply H _.
  assumption.
Qed.

goal _ (y : message) :
  (forall (x : message), P (x ++ x) => Q (x)) =>
  (P((y ++ zero) ++ (y ++ zero))) =>
  Q (y ++ zero).
Proof.
  intro H G.
  apply H _.
  assumption.
Qed.

(*------------------------------------------------------------------*)
abstract f : message -> message.
abstract g : message -> message.

goal _ (y,z : message) :
 (forall (x : message), P (x) => g (x) = f (x)) =>
 (forall (x : message), P (x)) =>
 (f(y) = f(<y,z>)) =>
 g (y) = g (<y,z>).
Proof.
  intro H G F.
  rewrite (H _ (%G (<_,_>))).
  rewrite (H _ (%G y)). 
  assumption F.
Qed.

goal _ (y,z : message) :
 (forall (x : message), P (x) => g (x) = f (x)) =>
 (forall (x : message), P (x)) =>
 g (<y,z>) = f (<y,z>).
Proof.
  intro H G.
  have U := H _ (%G (<y,z>)).
  assumption U.
Qed.

(*------------------------------------------------------------------*)
name a : message.
name b : message.

name c : message.
name d : message.

global goal _ :
  (Forall (t : timestamp), [happens(t)] -> equiv(diff(a,b), t)) ->
  equiv(diff(a,b)).
Proof.
  intro H.
  checkfail by apply H exn Failure.
  by apply H init. 
Qed.
