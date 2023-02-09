

channel c.

name na : message
name nb : message

abstract f : message -> message.

mutable s0 : message = zero.
mutable s1 (i : index) : message = na.

name n : index -> message.

process P(i : index) = 
  in(c,x);
  s0 := f(s0);
  s1(i) := f(s1(i));
  out(c,n(i)).

system !_i P(i).

set showStrengthenedHyp=true.

global goal _ (t : timestamp[const]) : equiv(empty) -> equiv(s0@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* using [na], we can deduce [s1] *)
global goal _ (t : timestamp[const], i : index[const]) : 
  equiv(na) -> equiv(s1(i)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* [nb] does not allow to conclude *)
global goal _ (t : timestamp[const], i : index[const]) : 
  equiv(nb) -> equiv(s0@t, s1(i)@t).
Proof. 
 checkfail (intro H; apply H) exn ApplyMatchFailure.
 checkfail (intro H; apply ~inductive H) exn ApplyMatchFailure.
Abort.

(* of course, both are simultaneously deducible *)
global goal _ (t : timestamp[const], i : index[const]) : 
  equiv(na) -> equiv(s0@t, s1(i)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* we can also deduce the sequence of all s1(i) *)
global goal _ (t : timestamp[const]) : 
  equiv(na) -> equiv(seq(i:index => s1(i)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* or even a try-find, since we can deduce all the tests, the then branches 
  and the else branch *)
global goal _ (t : timestamp[const]) : 
  equiv(na) -> 
  equiv(try find i such that s1(i)@t=zero in s1(i)@t else s0@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* this fails if we give `nb` instead of `na` *)
global goal _ (t : timestamp[const]) : 
  equiv(nb) -> 
  equiv(try find i such that s1(i)@t=zero in s1(i)@t else s0@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
 checkfail (intro H; apply ~inductive H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* from [frame@pred(t)], we can deduce [input@t] *)

global goal _ (t : timestamp[const]) : 
  [happens(t)] -> equiv(frame@pred(t)) -> equiv(input@t).
Proof. 
 intro Hap H; apply ~inductive H.
Qed.

global goal _ (t : timestamp[const]) : 
  [happens(t)] -> equiv(frame@pred(pred(t))) -> equiv(input@t).
Proof. 
 intro Hap H.
 checkfail (apply ~inductive H) exn ApplyMatchFailure.
Abort.

(* (* ------------------------------------------------------------------ *) *)
(* global goal _ (t : timestamp) : *)
(*   [happens(t)] -> *)
(*   equiv(frame@t) -> *)
(*   equiv(seq(t':timestamp -> if t' <= t then frame@t')). *)
(* Proof. *)
(*  intro Hap H; apply H. *)
(* Qed. *)
