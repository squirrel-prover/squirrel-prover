abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg : message -> message -> message
abstract f0 : message -> message
channel ch

system A: !_i in(ch,x);out(ch,<ok(i),x>).

system [bis] !_i in(ch,x);if x = a then out(ch,<ok(i),x>).

axiom [any] foo (x : message) : f(x) = a.

(*------------------------------------------------------------------*)
goal _ (x, y, z : message) :
  diff(<a,<f(y),a>>, e) = d =>
  diff(<f(x), <f(y), f(x)>>, e) = d.
Proof.
  intro H.
  rewrite foo.
  assumption.
Qed.

goal _ (x, y, z : message) :
  diff(<f(x),<a,f(x)>>, e) = d =>
  diff(<f(x), <f(y), f(x)>>, e) = d.
Proof.
  intro H.
  rewrite (foo y).
  assumption.
Qed.

(*------------------------------------------------------------------*)
(* when doing a *single* rewrite and an occurrence has been found
   below a diff, occurrences below a different diff projection are not
   rewritten. *)
goal _ (x, y, z : message) :
  diff(<a,<f(y),a>>, a) = d =>
  diff(<f(x), <f(y), f(x)>>, f(x)) = d.
Proof.
  intro H.
  rewrite foo.
  checkfail (by auto) exn GoalNotClosed.
Abort.

(* same as above, but valid. *)
goal _ (x, y, z : message) :
  diff(<a,<f(y),a>>, f(x)) = d =>
  diff(<f(x), <f(y), f(x)>>, f(x)) = d.
Proof.
  intro H.
  rewrite foo.
  assumption.
Qed.

(*------------------------------------------------------------------*)

axiom [default/left] foo_left (x : message) : f(x) = a.

goal _ (x, y, z : message) :
  diff(a, f(x)) = d =>
  diff(f(x), f(x)) = d.
Proof.
  intro H.
  rewrite foo_left.
  assumption.
Qed.

goal _ (x, y, z : message) :
  diff(<a,<f(y),a>>, e) = d =>
  diff(<f(x), <f(y), f(x)>>, e) = d.
Proof.
  intro H.
  rewrite foo_left.
  assumption.
Qed.

goal _ (x, y, z : message) :
  diff(<f(x),<a,f(x)>>, e) = d =>
  diff(<f(x), <f(y), f(x)>>, e) = d.
Proof.
  intro H.
  rewrite (foo y).
  assumption.
Qed.

(*------------------------------------------------------------------*)
axiom [default/right] foo_right (x : message) : f(x) = a.

goal _ (x, y, z : message) :
  diff(f(x), a) = d =>
  diff(f(x), f(x)) = d.
Proof.
  intro H.
  rewrite foo_right.
  assumption.
Qed.

(*------------------------------------------------------------------*)
goal _ (x, y, z : message) :
  diff(a, a) = d =>
  diff(f(x), f(x)) = d.
Proof.
  intro H.
  rewrite foo_left foo_right.
  assumption.
Qed.

goal _ (x, y, z : message) :
  diff(a, a) = d =>
  diff(f(x), f(x)) = d.
Proof.
  intro H.
  rewrite foo_right foo_left.
  assumption.
Qed.


goal _ (x, y, z : message) :
  diff(a, a) = d =>
  diff(f(x), f(x)) = d.
Proof.
  intro H.
  rewrite foo foo.
  assumption.
Qed.
