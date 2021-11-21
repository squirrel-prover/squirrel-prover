set autoIntro=false.

channel c.

name na : message
name nb : message
name n : index -> message
name m : index -> message

abstract f : message -> message.

mutable s0 (i    : index) : message = zero.
mutable s1 (i    : index) : message = na.
mutable s2 (i    : index) : message = n(i).
mutable s3 (i, j : index) : message = <n(i), n(j)>.
mutable s4 (i    : index) : message = m(i).
mutable s5 (i, j : index) : message = <n(i), m(j)>.

process P(i : index) = 
  in(c,x);
  s0(i)    := f(s0(i));
  s1(i)    := f(s1(i));
  s2(i)    := f(s2(i));
  s3(i, i) := f(s3(i, i));
  s4(i)    := f(s4(i));
  s5(i, i) := f(s5(i, i));
  out(c,zero).

system !_i P(i).

global goal _ (t : timestamp, i : index) : equiv(zero) -> equiv(s0(i)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* using [na], we can deduce [s1] *)
global goal _ (t : timestamp, i : index) : equiv(na) -> equiv(s0(i)@t, s1(i)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* [nb] does not allow to conclude *)
global goal _ (t : timestamp, i : index) :
  equiv(nb) -> equiv(s0(i)@t, s1(i)@t).
Proof.
 checkfail (intro H; apply ~inductive H) exn ApplyMatchFailure.
Abort.

(* using [na] and the sequence of all [n(j)], we can deduce [s0], [s1] and [s2] *)
global goal _ (t : timestamp, i : index) :
  equiv(na, seq(j:index -> n(j))) ->
  equiv(s0(i)@t, s1(i)@t, s2(i)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* idem, but with some seqs *)
global goal _ (t : timestamp) :
  equiv(na, seq(j:index -> n(j))) ->
  equiv(
    seq (i:index -> s0(i)@t),
    seq (i:index -> s1(i)@t),
    seq (i:index -> s2(i)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* idem, but with a single seq and some pairs *)
global goal _ (t : timestamp) :
  equiv(na, seq(j:index -> n(j))) ->
  equiv(seq (i:index -> <s0(i)@t, <s1(i)@t, s2(i)@t>>)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(*------------------------------------------------------------------*)
(* more complex tests *)

(* check that we can deduce terms using the FA rule *)
global goal _ (t : timestamp, i, j : index) :
  equiv(na, seq(j:index -> n(j))) -> equiv(s3(i, j)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* idem but putting everybody together *)
global goal _ (t : timestamp, i, j : index) :
  equiv(na, seq(j:index -> n(j))) -> equiv(s0(i)@t, s1(i)@t, s3(i, j)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* idem but with a seq *)
global goal _ (t : timestamp) :
  equiv(na, seq(j:index -> n(j))) ->
  equiv(
    seq (i:index -> s0(i)@t),
    seq (i:index -> s1(i)@t),
    seq (i:index -> s2(i)@t),
    seq (i,j:index -> s3(i,j)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* with spurious indices in sequences *)
global goal _ (t : timestamp) :
  equiv(na, seq(j:index -> n(j))) ->
  equiv(
    seq (i,k,l:index -> s0(i)@t),
    seq (i,k,l:index -> s1(i)@t),
    seq (i,k,l:index -> s2(i)@t),
    seq (i,j,k,l:index -> s3(i,j)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(*------------------------------------------------------------------*)
(* more complex tests, again *)

(* with some seqs *)
global goal _ (t : timestamp) :
  equiv(na, seq(j:index -> n(j)), seq(j:index -> m(j))) ->
  equiv(
    seq (i:index -> s0(i)@t),
    seq (i:index -> s1(i)@t),
    seq (i:index -> s2(i)@t),
    seq (i,j:index -> s3(i,j)@t),
    seq (i:index -> s4(i)@t),
    seq (i,j:index -> s5(i,j)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.


(*------------------------------------------------------------------*)
(* we give only the the nonce m(J) *)

global goal _ (t : timestamp, J : index) :
  equiv(na, m(J)) -> equiv(s4(J)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

global goal _ (t : timestamp, J : index) :
  equiv(na, m(J), seq(j:index -> n(j))) ->
  equiv(s4(J)@t, seq (i:index -> s5(i,J)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.

 intro H; apply ~inductive H.
Qed.

(* we cannot deduce any value of [s4] *)
global goal _ (t : timestamp, J : index) :
  equiv(na, m(J), seq(j:index -> n(j))) -> equiv(seq (i:index -> s4(i)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
 checkfail (intro H; apply ~inductive H) exn ApplyMatchFailure.
Abort.

(* idem for [s5] *)
global goal _ (t : timestamp, J : index) :
  equiv(na, m(J), seq(j:index -> n(j))) ->
  equiv(seq (i,j:index -> s5(i,j)@t)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
 checkfail (intro H; apply ~inductive H) exn ApplyMatchFailure.
Abort.

global goal _ (t : timestamp, J : index) :
  equiv(na, m(J), seq(j:index -> n(j))) ->
  equiv(na, m(J), seq(j:index -> n(j)), f(<na,seq (i:index -> s4(i)@t)>)).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
 checkfail (intro H; apply ~inductive H) exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
(* pure trace model formulas are always deducible by the adversary *)
(* note that this has been integrated in the standard apply *)

global goal _ (i, j : index):
  equiv(zero) ->
  equiv (i = j).
Proof.
  intro H; apply H.
Qed.

global goal _ :
  equiv(zero) ->
  equiv (seq(i,j:index -> i = j)).
Proof.
  intro H; apply H.
Qed.

global goal _ :
  equiv(zero) ->
  equiv (seq(i,j:index -> if (i = j) && (j = j) then zero else empty)).
Proof.
  intro H; apply H.
Qed.
