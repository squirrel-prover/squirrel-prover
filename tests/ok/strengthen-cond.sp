include Core.

senc enc,dec

abstract accept : message

abstract cinit : message

abstract mpid: index -> message

name sid: index -> message

name k: index -> message

(*------------------------------------------------------------------*)
(* counters *)
mutable SCtr(i:index) : message = cinit

(*------------------------------------------------------------------*)
channel cS

abstract (~<): message -> message -> boolean.

(*------------------------------------------------------------------*)

mutex l : 1.

process server (i:index) =
  in(cS,x);
  let cipher = snd(snd(x)) in
  let deccipher = dec(cipher,k(i)) in
  let xcpt = snd(deccipher) in
  lock l(i);
  if SCtr(i) ~< xcpt then
    SCtr(i) := xcpt;
    unlock l(i);
    out(cS,accept)
  else
    unlock l(i).

(* note: U's cannot be computed by the adversary if he does not already
   know it (e.g. by giving him the frame *)
process U = new m; out(cS, m).

system !_i (U | !_j server(j)).

(*------------------------------------------------------------------*)
set showStrengthenedHyp=true.

(*------------------------------------------------------------------*)
global lemma _ (t : timestamp[const]):
  [happens(t)] ->
  equiv(frame@t, seq(pid:index => k(pid))) ->
  equiv(
    frame@t,
    seq(pid:index => k(pid)),
    seq(pid:index => SCtr(pid)@t)).
Proof.
  intro Hap H.

 checkfail (apply H) exn ApplyMatchFailure.
 by apply ~inductive H.
Qed.

(* fails if `t` is non-det *)
global lemma _ (t : timestamp):
  [happens(t)] ->
  equiv(frame@t, seq(pid:index => k(pid))) ->
  equiv(
    frame@t,
    seq(pid:index => k(pid)),
    seq(pid:index => SCtr(pid)@t)).
Proof.
  intro Hap H.

 checkfail (apply H) exn ApplyMatchFailure.
 checkfail apply ~inductive H exn ApplyMatchFailure.
Abort.

(*------------------------------------------------------------------*)
global lemma _ (t : timestamp[const]):
  [happens(t)] -> 
  equiv(
    frame@t,
    seq(pid:index => sid(pid)),
    seq(pid:index => k(pid))
  ).
Proof.
  dependent induction t => t Hind Hap.
  enrich seq(pid:index => SCtr(pid)@t).

  case t => Eq; 
  try (repeat destruct Eq as [_ Eq]; 
       rewrite /*;
       by apply ~inductive Hind (pred(t))).
  
  + by rewrite /* in 1. 

  (* case `t = U(i)`, which cannot be proved because of `m(i)` *)
  + destruct Eq as [i Eq].
    rewrite /*.
    fa <_,_>. fa <_,_>. fa (if _ then _).
    (* check that `t = U(i)` *)
    assert (t = U(i)) as _ by auto.
    (* remove the undeducible term m(i) and check that we can conclude 
       without it *)
    assert m(i) = zero as -> by admit.
    by apply ~inductive Hind (pred(t)).
Qed.

global lemma _ (t : timestamp[const]):
  [happens(t)] ->
  equiv(frame@t) ->
  equiv(
    frame@t,
    seq(pid:index => k(pid)),
    seq(pid:index => SCtr(pid)@t)).
Proof.
  intro Hap H.
  checkfail apply H exn ApplyMatchFailure.
Abort.
