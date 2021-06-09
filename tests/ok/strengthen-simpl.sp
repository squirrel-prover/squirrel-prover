set autoIntro=false.

channel c.

name na : message
name nb : message
name n : index -> message
name m : index -> message

abstract f : message -> message.

mutable s0 : message = zero.
mutable s1 (i : index) : message = na.

process P(i : index) = 
  in(c,x);
  s0 := f(s0);
  s1(i) := f(s1(i));
  out(c,zero).

system !_i P(i).

equiv _ (t : timestamp) : empty -> s0@t.
Proof.
 intro H; apply H.
Qed.

(* using [na], we can deduce [s1] *)
equiv _ (t : timestamp, i : index) : na -> s1(i)@t.
Proof.
 intro H; apply H.
Qed.

(* [nb] does not allow to conclude *)
equiv _ (t : timestamp, i : index) : nb -> s0@t, s1(i)@t.
Proof. 
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(* of course, both are simultaneously deducible *)
equiv _ (t : timestamp, i : index) : na -> s0@t, s1(i)@t.
Proof.
 intro H; apply H.
Qed.

(* we can also deduce the sequence of all s1(i) *)
equiv _ (t : timestamp) : na -> seq(i -> s1(i)@t).
Proof.
 intro H; apply H.
Qed.

(* or even a try-find, since we can deduce all the tests, the then branches 
  and the else branch *)
equiv _ (t : timestamp) : 
na -> 
 try find i such that s1(i)@t=zero in s1(i)@t else s0@t.
Proof.
 intro H; apply H.
Qed.

(* this fails if we give `nb` instead of `na` *)
equiv _ (t : timestamp) : 
nb -> 
 try find i such that s1(i)@t=zero in s1(i)@t else s0@t.
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.
