abstract a : message
abstract b : message
abstract c : message
abstract d : message
abstract e : message

name n1 : index -> message
name m1 : message
name m2 : message

abstract ok : index   -> message
abstract f  : message -> message
abstract gg : message * message -> message
abstract f0 : message -> message
channel ch

mutable s : message = empty.

system A: !_i in(ch,x); new l; out(ch,<ok(i),<x,l>>).

system [bis] !_i in(ch,x); new l; if x = a then out(ch,<ok(i),<x,l>>).


(* This is a weakness of bideduction in Squirrel: 
   It does not exploit the fact that `(u|phi)` is
   always deductible when phi is `false`.*)
global lemma _ :
  equiv(if false then m2 else a).
Proof.
  checkfail (deduce 0) exn ApplyMatchFailure.
Abort.

(* The condition is not deductible *)
global lemma _ : 
  equiv(if m2=a then true else false).
Proof.
  checkfail (deduce 0) exn ApplyMatchFailure.
Abort.

(* The left branch is not deductible *)
global lemma _ : 
  equiv(if a=b then m2 else a).
Proof.
  checkfail (deduce 0) exn ApplyMatchFailure.
Abort.

(* The right branch is not deductible *)
global lemma _ : 
  equiv(if a=b then c else m2).
Proof.
  checkfail (deduce 0) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
global lemma _ (t:timestamp) :
  equiv(if false then frame@t else empty) -> equiv(frame@t).
Proof.
  checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* The condition is taken into account for deduction*)
global lemma _ (t:timestamp) :
  equiv(frame@t)-> [happens(t)] -> equiv(if exec@pred(t) then output@pred(t) else a).
Proof.
  intro H.
  intro H1.
  apply H.
Qed.

(* here, the if-then-else is in the wrong direction, hence the application fails *)
global lemma _ (t:timestamp) :
  equiv(frame@t)-> [happens(t)] -> equiv(if exec@pred(t) then a else output@pred(t)).
Proof.
  intro H.
  intro H1.
  checkfail apply H exn ApplyMatchFailure.
Abort.

global lemma _ (t:timestamp) :
  equiv(frame@t)-> [happens(t)] -> equiv(if not(exec@pred(t)) then a else output@pred(t)).
Proof.
  intro H.
  intro H1.
  apply H.
Qed.





