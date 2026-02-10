(* This file shows artificial examples where the old crypto failed.
   The new tactic succeeds thanks to memoization alone.
   We illustrate at the end of the file a case where time sensitivity
   is required too. *)

include Core.

(** Simple XOR game without log, where a new name n1 is used to hide
    the parameter of the o_xor oracle for each new oracle call. *)
game XOR_SINGLE = {
  oracle o_xor(x: message) = {
    rnd n1: message;
    rnd n2: message;
    return if len n1 = len x then diff(xor n1 x, n2)
  }
}.

(* --------------------------------------------------------- *)

(** # Example with fixed input and replicated output *)

name n : message.
name m : message.

abstract msg : message.
axiom msg_len @system:any : len n = len msg.

channel c.

(** Simple example where `xor n msg` is outputted multiple times
    on the left; on the right, `m` is output multiple times instead.
    Simulating this using XOR_SINGLE requires memoizing the oracle
    output, but time sensitivity is not needed. *)
system S = !_i out(c, diff(xor n msg, m)).

global lemma _ @system:S (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro H.
  (* Crypto cannot succeed without memoization. *)
  checkfail (crypto ~no_memoization XOR_SINGLE; 1: smt) exn Failure.
  crypto XOR_SINGLE.
  - smt.
  - intro *; apply msg_len.
Qed.

(* --------------------------------------------------------- *)

(** # Variant with chosen input *)

system S_chosen =
  in(c,x); !_i out(c, if len n = len x then diff(xor n x, m)).

global lemma _ @system:S_chosen (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro H.
  checkfail (crypto ~no_memoization XOR_SINGLE; smt) exn Failure.
  crypto XOR_SINGLE; smt.
Qed.

(* --------------------------------------------------------- *)

(** # Variant with multiple outputs in sequence and chosen input *)

abstract f : message*message -> message.

system S_sequence =
  in(c,x);
  out(c, if len n = len x then diff(xor n x, m));
  in(c,y);
  out(c, f(y, if len n = len x then diff(xor n x, m))).

global lemma _ @system:S_sequence (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro H.
  checkfail (crypto ~no_memoization XOR_SINGLE; smt) exn Failure.
  crypto XOR_SINGLE; smt.
Qed.

(* --------------------------------------------------------- *)

(** # Variant with multiple outputs and fixed input *)

system S_bis =
  out(c,diff(xor n msg, m));
  in(c,y);
  out(c,f(y,diff(xor n msg, m))).

global lemma _ @system:S_bis (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro H.
  crypto XOR_SINGLE; try smt. intro *; apply msg_len.
Qed.

(* --------------------------------------------------------- *)

(** # Similar example relying on PRF requires time sensitivity *)

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

name k : kty.

system T = new nfresh; !_i out(c, diff(nfresh, h(empty,k))).

global lemma _ @system:T (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro H.
  (* A time sensitive invariant is required to justify bi-deduction. *)
  checkfail (crypto PRF (key:k); smt) exn Failure.
  crypto ~time_sensitive PRF (key:k); smt.
Qed.
