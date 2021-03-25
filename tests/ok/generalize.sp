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

system A: !_i in(ch,x);out(ch,(ok(i),x)).

goal _ :
 (forall (x,y : message), x = a || y = b) =>
 (forall (y,x : message), x = a || y = b).
Proof.
  intro Ass y x.
  generalize y x.
  assumption.
Qed.
