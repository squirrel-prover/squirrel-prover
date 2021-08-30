set autoIntro=false.

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
process server (i:index) =
  in(cS,x);
  let cipher = snd(snd(x)) in
  let deccipher = dec(cipher,k(i)) in
  let xcpt = snd(deccipher) in
  if SCtr(i) ~< xcpt then
  SCtr(i) := xcpt;
  out(cS,accept).

system !_i !_j server(j).

(*------------------------------------------------------------------*)
global goal _ (t : timestamp):
  [happens(t)] ->
  equiv(frame@t, seq(pid:index -> k(pid))) ->
  equiv(
    frame@t,
    seq(pid:index -> k(pid)),
    seq(pid:index -> SCtr(pid)@t)).
Proof.
  intro Hap H.
  apply H.
Qed.


set showStrengthenedHyp=true.
global goal _ (t : timestamp):
  [happens(t)] -> 
  equiv(
    frame@t,
    seq(pid:index -> sid(pid)),
    seq(pid:index -> k(pid))
  ).
Proof.
  dependent induction t => t Hind Hap.
  enrich seq(pid:index -> SCtr(pid)@t).

  case t => Eq; 
  try (repeat destruct Eq as [_ Eq]; 
       rewrite /* in 1;
       by apply Hind (pred(t))).
  
  by rewrite /* in 1. 
Qed.

global goal _ (t : timestamp):
  [happens(t)] ->
  equiv(frame@t) ->
  equiv(
    frame@t,
    seq(pid:index -> k(pid)),
    seq(pid:index -> SCtr(pid)@t)).
Proof.
  intro Hap H.
  checkfail apply H exn ApplyMatchFailure.
Abort.
