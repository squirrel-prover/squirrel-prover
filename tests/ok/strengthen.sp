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

equiv _ (t : timestamp, i : index) : zero -> s0(i)@t.
Proof.
 intro H; apply H.
Qed.

(* using [na], we can deduce [s1] *)
equiv _ (t : timestamp, i : index) : na -> s0(i)@t, s1(i)@t.
Proof.
 intro H; apply H.
Qed.

(* [nb] does not allow to conclude *)
equiv _ (t : timestamp, i : index) : nb -> s0(i)@t, s1(i)@t.
Proof. 
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(* using [na] and the sequence of all [n(j)], we can deduce [s1] and [s2] *)
equiv _ (t : timestamp, i : index) :
  na, seq(j -> n(j)) -> s0(i)@t, s1(i)@t, s2(i)@t.
Proof.
 intro H; apply H.
Qed.

(* idem, but with some seqs *)
equiv _ (t : timestamp) :
  na, seq(j -> n(j)) ->
  seq (i -> s0(i)@t),
  seq (i -> s1(i)@t),
  seq (i -> s2(i)@t).
Proof.
 intro H; apply H.
Qed.

(* idem, but with a single seq and some pairs *)
equiv _ (t : timestamp) :
  na, seq(j -> n(j)) ->
  seq (i -> <s0(i)@t, <s1(i)@t, s2(i)@t>>).
Proof.
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* more complex tests *)

(* check that we can deduce terms using the FA rule *)
equiv _ (t : timestamp, i, j : index) :
  na, seq(j -> n(j)) -> s3(i, j)@t.
Proof.
 intro H; apply H.
Qed.

(* idem but putting everybody together *)
equiv _ (t : timestamp, i, j : index) :
  na, seq(j -> n(j)) -> s0(i)@t, s1(i)@t, s3(i, j)@t.
Proof.
 intro H; apply H.
Qed.

(* idem but with a seq *)
equiv _ (t : timestamp) :
  na, seq(j -> n(j)) ->
  seq (i -> s0(i)@t),
  seq (i -> s1(i)@t),
  seq (i -> s2(i)@t),
  seq (i,j -> s3(i,j)@t).
Proof.
 intro H; apply H.
Qed.

(* with spurious indices in sequences *)
equiv _ (t : timestamp) :
  na, seq(j -> n(j)) ->
  seq (i,k,l -> s0(i)@t),
  seq (i,k,l -> s1(i)@t),
  seq (i,k,l -> s2(i)@t),
  seq (i,j,k,l -> s3(i,j)@t).
Proof.
 intro H; apply H.
Qed.

(*------------------------------------------------------------------*)
(* more complex tests, again *)

(* with some seqs *)
equiv _ (t : timestamp) :
  na, seq(j -> n(j)), seq(j -> m(j)) ->
  seq (i -> s0(i)@t),
  seq (i -> s1(i)@t),
  seq (i -> s2(i)@t),
  seq (i,j -> s3(i,j)@t),
  seq (i -> s4(i)@t),
  seq (i,j -> s5(i,j)@t).
Proof.
 intro H; apply H.
Qed.


(*------------------------------------------------------------------*)
(* we give only the the nonce m(J) *)

equiv _ (t : timestamp, J : index) :
  na, m(J) -> s4(J)@t.
Proof.
 intro H; apply H.
Qed.

equiv _ (t : timestamp, J : index) :
  na, m(J), seq(j -> n(j)) ->
  s4(J)@t,
  seq (i -> s5(i,J)@t).
Proof.
 intro H; apply H.
Qed.

(* we cannot deduce any value of [s4] *)
equiv _ (t : timestamp, J : index) :
  na, m(J), seq(j -> n(j)) -> seq (i -> s4(i)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

(* idem for [s5] *)
equiv _ (t : timestamp, J : index) :
  na, m(J), seq(j -> n(j)) -> 
  seq (i,j -> s5(i,j)@t).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

equiv _ (t : timestamp, J : index) :
  na, m(J), seq(j -> n(j)) -> na, m(J), seq(j -> n(j)), f(<na,seq (i -> s4(i)@t)>).
Proof.
 checkfail (intro H; apply H) exn ApplyMatchFailure.
Abort.

