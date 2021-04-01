set autoIntro=false.

abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg  : message -> message -> message
abstract f0  : message -> message
channel ch

system A: !_i in(ch,x);out(ch,<ok(i),x>).

system [bis] !_i in(ch,x);if x = a then out(ch,<ok(i),x>).

goal _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(f0(<x,y>)).
Proof.
  intro x y i H Hyp.
  apply Hyp.
  assumption.
Qed.

(* same goal, but slightly changing the conclusion to prevent application  *)
goal _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(<x,y>).
Proof.
  intro x y j H Hyp.
  checkfail (apply Hyp) exn ApplyMatchFailure.
Abort.

(* all variables of the lemma are not bound by the lemma application  *)
goal _ (x, y : message, i : index) : 
  f0(<x,y>) = ok(i) =>
  (forall (x,y : message, i : index), x = ok(i) => gg(f(x),y) = f0(x)) =>
  gg(f(f0(<x,y>)),<y,y>) = f0(<x,y>).
Proof.
  intro x y j H Hyp.
  checkfail (apply Hyp) exn ApplyBadInst.
Abort.


(* Test `apply ... in ...`  *)
goal _ (A,B,C,D : boolean, y : message, j : index) : 
  A => B => C => (D => False) =>
  (forall (x : message, i : index), A => x = ok(i) => B => D) =>
  (C => f(y) = ok(j)) => False.
Proof.
  intro A B C D y j Ha Hb Hc Hfinal H Hin.
  apply H in Hin;
  [1,2,3: assumption |
   4: by apply Hfinal]. 
Qed.
