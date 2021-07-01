set autoIntro=false.

channel c.

name na : message
name nb : message

abstract f : message -> message.

mutable s0 : message = zero.
mutable s1 (i : index) : message = na.

process P(i : index) = 
  in(c,x);
  s0 := f(s0);
  s1(i) := f(s1(i));
  out(c,zero).

system !_i P(i).

global goal _ (t : timestamp) : equiv(empty) -> equiv(s0@t).
Proof.
 intro H; apply H.
Qed.

(* using [na], we can deduce [s1] *)
global goal _ (t : timestamp, i : index) : equiv(na) -> equiv(s1(i)@t).
Proof.
 intro H; apply H.
Qed.

(* [nb] does not allow to conclude *)
global goal _ (t : timestamp, i : index) : equiv(nb) -> equiv(s0@t, s1(i)@t).
Proof. 
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(* of course, both are simultaneously deducible *)
global goal _ (t : timestamp, i : index) : equiv(na) -> equiv(s0@t, s1(i)@t).
Proof.
 intro H; apply H.
Qed.

(* we can also deduce the sequence of all s1(i) *)
global goal _ (t : timestamp) : equiv(na) -> equiv(seq(i -> s1(i)@t)).
Proof.
 intro H; apply H.
Qed.

(* or even a try-find, since we can deduce all the tests, the then branches 
  and the else branch *)
global goal _ (t : timestamp) : 
  equiv(na) -> 
  equiv(try find i such that s1(i)@t=zero in s1(i)@t else s0@t).
Proof.
 intro H; apply H.
Qed.

(* this fails if we give `nb` instead of `na` *)
global goal _ (t : timestamp) : 
  equiv(nb) -> 
  equiv(try find i such that s1(i)@t=zero in s1(i)@t else s0@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.
