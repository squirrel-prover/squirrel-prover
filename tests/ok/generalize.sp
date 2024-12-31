abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

abstract ok : index   -> message
abstract f  : message -> message
channel ch

system A: !_i in(ch,x);out(ch,<ok(i),x>).

abstract even : message -> boolean.

(*------------------------------------------------------------------*)
(* reach *)

lemma _ :
 (forall (x,y : message), x = a || y = b) =>
 (forall (x,y : message), y = a || x = b).
Proof.
  intro Ass x y.
  generalize y x. 
  assumption Ass.
Qed.

lemma _ :
 (forall (u,v : message), u = a || v = b) =>
 (forall (x,y : message), x = a || y = b).
Proof.
  intro Ass x y.
  generalize x y as u v.
  assumption Ass.
Qed.

lemma _ :
 (forall (x,y : message), x = a || y = b) =>
 (forall (y,x : message), f(x) = a || f(y) = b).
Proof.
  intro Ass y x.
  generalize (f x) (f y) as x y.
  assumption Ass.
Qed.

lemma _ :
 (forall (x,y : message), x = a || y = b) =>
 (forall (y,x : message), f(x) = a || f(y) = b).
Proof.
  intro Ass y x.
  generalize (f _) (f _) as u v.
  assumption Ass.
Qed.

lemma _ :
 (forall (x,y : message), x = a || y = b) =>
 (forall (y,x : message), f(x) = a || f(y) = b).
Proof.
  intro Ass y x.
  generalize (f x) (f _) as u v.
  assumption Ass.
Qed.

lemma _ (z : message) :
 (forall (x,z:message), (forall (y:message), y = z) => even(x)) =>
 (forall (y : message), y = z) =>
 (forall (x : message), even(x)).
Proof.
  intro Hyp Ass x.
  generalize dependent x z as x z. 
  checkfail have A := Ass exn Failure. (* no goal named `Ass` *)
  assumption Hyp.
Qed.

(*------------------------------------------------------------------*)
abstract P : message -> bool.

axiom foo_const (x : message[const]) : P x.

global lemma _ (z : message[const]) : [P z].
Proof.
  byequiv. 
  apply foo_const.
Qed.

(* check that local sequent loose tags when generalizing a local quantifier  *)
global lemma _ (z : message[const]) : [P z].
Proof.
  byequiv. 
  generalize z => z.
  checkfail apply foo_const exn Failure.
Abort.

(*------------------------------------------------------------------*)
axiom foo_glob (x : message[glob]) : P x.

global lemma _ x : [P x].
Proof.
  generalize x => x.
  apply foo_glob.
Qed.

global lemma _ t : [P (frame@t)].
Proof. 
  generalize (frame@t) => x.
  checkfail apply foo_glob exn Failure. (* bad variabe instantiation *)
Abort.

(*------------------------------------------------------------------*)
lemma [any] _ ['a 'b] (phi,phi': 'a -> _): 
  (forall (u,v:bool), u && v) =>
  (exists i, phi i) && exists i, phi' i.
Proof.
  intro Ass.
  generalize (exists _, _) (exists _, _) as u v.
  assumption Ass.
Qed.
