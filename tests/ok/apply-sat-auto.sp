(* Tests of the use of satisfiability (constraints) in the 
   bi-deduction *)

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

(* set debugConstr=true. *)

lemma _ (t,t' : timestamp):
  happens(t) && t=t' => (t<=t').
Proof.
  constraints.
Qed.

(* simple sanity check *)
lemma _ (t,t' : timestamp):
  happens(t) && t=t' => (t' < t).
Proof.
  checkfail constraints exn Failure.
Abort.

(*------------------------------------------------------------------*)
global lemma _ (t,t' :timestamp[const]) :
  [happens(t)] -> 
  equiv(frame@t) -> 
  equiv(if t=t' then frame@t' else frame@t).
Proof.
  intro Hhap H.
  apply H.
Qed.

global lemma _ (t,t' :timestamp[const]) :
  [happens(t)] -> 
  equiv(frame@t) -> 
  equiv(if t<>t' then frame@t' else frame@t).
Proof.
  intro Hhap H.
  checkfail apply H exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
global lemma _ (t:timestamp[const]) :
  [happens(t)] -> 
  equiv(frame@t) -> 
  equiv(frame@pred(t),exec@pred(t)).
Proof.
  intro Hhap H.
  apply H.
Qed.

global lemma _ (t:timestamp[const]) :
  [happens(t)] -> 
  equiv(frame@t) -> 
  equiv(frame@pred(t),exec@pred(t) && empty=output@pred(t)).
Proof.
  intro Hhap H.
  apply H.
Qed.




