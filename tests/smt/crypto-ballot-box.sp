(* SMT: Z3 4.13.0 *)

include Core.

set timeout = 10.


(* A type seed, for any ponctual randomness (in signature and encryption *)
type seed[large].

(* ------------------------------------------------------------------- *)
(* Encryption *)
type sk_enc[large].
type pk_enc.
type ctxt.
abstract pk_enc : sk_enc -> pk_enc.
abstract encr : message -> pk_enc -> seed -> ctxt.
abstract decr : ctxt -> sk_enc -> message.

(* ------------------------------------------------------------------- *)
(* Format and read function to convert values to type message. *)
abstract format ['a] : 'a -> message.
abstract read ['a] : message -> 'a.

(* ------------------------------------------------------------------- *)
(* Formatting axioms *)

axiom [any] format_encr    (x : ctxt) : read (format x) = x.
hint rewrite format_encr.


(*******************************************************************************
# Security games
*******************************************************************************)

(* CCA2 *)
game CCA2 = {
  rnd key : sk_enc;
  var log = empty_set;
  oracle pk = {
    return pk_enc key
  }
  oracle encrypt (m0,m1 : message) = {
    rnd seed: seed;
    var c0 = encr m0 (pk_enc key) seed;
    var c1 = encr m1 (pk_enc key) seed;
    log := add (format diff(c0,c1)) log ;
    return encr diff(m0,m1) (pk_enc key) seed
  }
  oracle decrypt (c : ctxt) = {
    return if not (mem (format c) log) then decr c key
  }
}.


channel c.
abstract  m:message.
name s:seed.
name sk:sk_enc.
abstract ko:message.
abstract ok:message.

process Send = 
  out(c, format (encr diff(zero,m) (pk_enc sk) s)).

process Store (i:index)=
  in(c,mess);
  out(c,  format (mess= format (encr diff(zero,m) (pk_enc sk) s))).



process Store_or_drop (i:index)=
  in(c,mess);
  if mess = format (encr diff(zero,m) (pk_enc sk) s) then
   out(c,  ok)
  else
   out(c,ko).


system S0= (Send | !_i Store(i)).
system S1= (Send | !_i Store_or_drop(i)).

global lemma [S0] _ (t:timestamp[const]): 
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto CCA2 => //.
+ smt.
+ smt.
Qed.

global lemma [S1] _ (t:timestamp[const]): 
[happens(t)] -> equiv(frame@t).
Proof.
intro *.
crypto CCA2 => //.
+ smt.
+ smt.
+ smt.
+ smt.
+ smt.
Qed.    

