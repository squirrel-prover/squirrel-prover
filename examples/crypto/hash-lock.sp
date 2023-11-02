(* A simple analysis of the Hash-Lock protocol,
   following the paper's running example. *)

include Basic.

(* Assume a binary function h, which we will use a a keyed hash function,
   assuming PRF.
   Note that we don't need to declare kty as as large type, but the
   crypto assumption on h implies that kty is large -- otherwise
   the attacker could brute force the crypto games. *)

type kty.
abstract h : message * kty -> message.

game PRF = {
  rnd key : kty;
  var lhash = empty_set; (* Log for ohash queries.     *)
  var lchal = empty_set; (* Log for challenge queries. *)

  oracle ohash x = {
    lhash := add x lhash;
    return if mem x lchal then zero else h(x,key)
  }

  oracle challenge x = {
    rnd r : message;
    var old_lchal = lchal;
    lchal := add x lchal;
    return if mem x old_lchal || mem x lhash then zero else diff(r, h(x,key))
  }
}.

(* --------------------------------------------------------- *)

(* Model of Hash-lock protocol:
   many agents with their own keys, that output for each session
   a fresh name and the hash of this name using their keys.  *)

name key : index -> kty.
name dummy : message.
channel c.

process Agent(i:index,k:index) =
  in(c,x);
  new nT;
  out(c, <nT, h(<nT,x>,key(i))>).

system [HashLock]  (!_i !_j A: Agent(i,j)).

(* Proof that at any time `t`,
   given the sequence of all message outputted before that time,
   the attacker cannot distinguish the hash part of the output at `t`
   from a fresh name.*)
global lemma [HashLock] _ (i,j:index[adv]) :
  equiv(frame@pred(A(i,j)),
        <nT(i,j),
         diff(h(<nT(i,j),input@A(i,j)>,key(i)),
              dummy)>).
Proof.
  expandall.
  fa 1. sym.
  crypto PRF (key:key(i)) => //.
Qed.
