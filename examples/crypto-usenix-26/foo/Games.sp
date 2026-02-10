include Core.

(*******************************************************************************
# Preliminary definitions (primitives, types)
*******************************************************************************)
type seed[serializable,large].

(* ------------------------------------------------------------------- *)
(* Encryption *)
type sk_enc[serializable,large].
type pk_enc[serializable].
type ctxt[serializable].

op pk_enc : sk_enc -> pk_enc.
op encr : message -> pk_enc -> seed -> ctxt.
op decr : ctxt -> sk_enc -> message.

axiom decr_encr @system:any m r sk : decr (encr m (pk_enc sk) r) sk = m.

(* ------------------------------------------------------------------- *)
(* Commitment *)
type k_comm[serializable,large].
op comm  : message -> k_comm -> message.
op copen : message -> k_comm -> message.

axiom copen_comm @system:any x k : copen (comm x k) k = x.


(* ------------------------------------------------------------------- *)
(* shuffling function *)
op shuffle : (index -> message) -> message.

(* ------------------------------------------------------------------- *)
(* Blind signatures *)

type pk_sign[serializable].            (* public verification key *)
type sk_sign[serializable,large].      (* secret signing key *) 
type token_bsign[serializable,large].  (* blinding token, sampled by the voters *) 
type blinded[serializable].            (* blinded message, to be signed *) 
type bsigned[serializable].            (* blinded signature *) 
type signed[serializable].             (* unblinded signature *) 

(* `pk ← bskg(sk)` generates the public key `pk` associated 
   to the secret key `sk` *)
op bskg : sk_sign -> pk_sign.

(* `b ← blind(m,pk,t)` computes the blinding `b` of a message `m` *)
op blind    : message -> pk_sign -> token_bsign -> blinded.

(* `bs ← bsign(b,sk,r)` computes the blinded signature of the blinded
   message `b` *)
op bsign    : blinded -> sk_sign -> seed -> bsigned.

(* `acc ← baccept(m,pk,t,bs)` checks if `bs` is a blinded signature
   for message `m` *)
op baccepte : message -> pk_sign -> token_bsign -> bsigned -> bool. 

(* `ub ← unblind(m,pk,t,bs)` unblinds the blinded signature `bs` 
   of message `m` using the blinding token `t` *)
op unblind  : message -> pk_sign -> token_bsign -> bsigned -> signed.

(* `ver ← bverif(m,ub,pk)` checks if `ub` is an unblinded 
   signature of `m` *)
op bverif   : message -> signed -> pk_sign -> bool. 

(* ------------------------------------------------------------------- *)
(* Format and read function to convert values to type message. *)
op format ['a] : 'a -> message.
op read   ['a] : message -> 'a.


(* ------------------------------------------------------------------- *)
(* operator for ballot box *)
op mem_bb ((c,s):message*signed) (bb : (index -> (message*signed))) = 
  exists i, bb(i) = (c,s).

op find_bb ((c,s):(message*signed)) (bb: (index -> (message*signed))) = 
  try find i such that bb i = (c,s) in i else witness.

(* ------------------------------------------------------------------- *)


(* Formatting axioms *)

(*axiom format_pkb (pk:pk_bsign) : read_pkb (format_pkb pk) = pk.*)
axiom [any] format_blind   (x : blinded                     ) : read (format x) = x.
hint rewrite format_blind.
axiom [any] format_bsign   (x : bsigned                     ) : read (format x) = x.
hint rewrite format_bsign.
axiom [any] format_pk_sign (x : pk_sign                     ) : read (format x) = x.
hint rewrite format_pk_sign.
axiom [any] format_sign    (x : signed                      ) : read (format x) = x.
hint rewrite format_sign.
axiom [any] format_encr    (x : ctxt                        ) : read (format x) = x.
hint rewrite format_encr.
axiom [any] format_pk_enc  (x : pk_enc                      ) : read (format x) = x.
hint rewrite format_pk_enc.
axiom [any] format_kc      (x : k_comm                      ) : read (format x) = x.
hint rewrite format_kc.
axiom [any] format_bb      (x : (index -> (message*signed)) ) : read (format x) = x.
hint rewrite format_bb.
axiom [any] format_index   (x : index                       ) : read (format x) = x.
hint rewrite format_index.

axiom [any] format_inj ['a] (x,y:'a) : format x = format y => x = y.

axiom [any] read_encr (x:message): format (read[ctxt] x) = x.

(* ------------------------------------------------------------------- *)
(* Operator for the injective and surjective properties *)

op injective ['a 'b] (f : 'a -> 'b) = forall i j, f(i) = f(j) => i = j.

op partial_injective ['b] (f:index -> 'b) (A: index -> timestamp) = 
forall i j, (happens(A(i)) && happens(A(j))) => (f(i) = f(j)) => (i=j).

op surjective ['a 'b] (f : 'a -> 'b) = forall b, exists a, f a = b.

(*******************************************************************************
# Security games
*******************************************************************************)

(* check whether we called the unblinding oracle. *)
op was_queried log = mem (format true) log.

(* log that the unblinding oracle has been called. *)
op query log = add (format true) log.

(*------------------------------------------------------------------*)
game Blindness = {
  rnd token0 : token_bsign;
  rnd token1 : token_bsign;

  (* `log` is empty untill we call the `unblind` oracle *)
  var log = empty_set;

  let m0 = #init;
  let m1 = #init;
  let pk = #init;

  oracle blindingA = {
    return blind diff(m0,m1) pk token0;
  }

  oracle blindingB = {
    return blind diff(m1,m0) pk token1;
  }

  oracle unblind (sA,sB : bsigned) = {

   (* make sure that we did not already query `unblind` *)
   var can_call = not (was_queried log);

   var accA = baccepte diff(m0,m1) pk token0 sA;
   var accB = baccepte diff(m1,m0) pk token1 sB;
   var ub0 = unblind m0 pk diff(token0,token1) diff(sA,sB);
   var ub1 = unblind m1 pk diff(token1,token0) diff(sB,sA);

   (* preven future queries to `unblind` *)
   log := query log;

   return
     if can_call then
       if accA && accB 
       then (format ub0, format ub1)
       else witness
     else witness
   }
}.

(*------------------------------------------------------------------*)
(* The Selective-Failure Blindness game, see:

   Security of Blind Signatures Under Aborts
   Marc Fischlin and Dominique Schröder
   Public Key Cryptography 2009

   https://www.iacr.org/archive/pkc2009/54430301/54430301.pdf
 *)
game SelectiveFailureBlinding = {
  rnd token0 : token_bsign;
  rnd token1 : token_bsign;

  (* `log` is empty untill we call the `unblind` oracle *)
  var log = empty_set;

  let m0 = #init;
  let m1 = #init;
  let pk = #init;

  oracle blindingA = {
    return blind diff(m0,m1) pk token0;
  }

  oracle blindingB = {
    return blind diff(m1,m0) pk token1;
  }

  oracle unblind (sA,sB : bsigned) = {

   (* make sure that we did not already query `unblind` *)
   var can_call = not (was_queried log);

   var accA = baccepte diff(m0,m1) pk token0 sA;
   var accB = baccepte diff(m1,m0) pk token1 sB;
   var ub0 = unblind m0 pk diff(token0,token1) diff(sA,sB);
   var ub1 = unblind m1 pk diff(token1,token0) diff(sB,sA);

   (* preven future queries to `unblind` *)
   log := query log;

   return
     if can_call then
       if accA && accB 
       then (format ub0, format ub1, accA, accB)
       else (zero, zero, accA, accB)
     else witness
   }
}.

(*------------------------------------------------------------------*)
(* The Adaptative Selective-Failure Blindness game, whose security can
   be reduced to that of Selective-Failure Blindness. *)

(* This is a non-trivial encoding of the Adaptative Selective-Failure
   Blindness game that is written in such a way as to help the
   `crypto` proof-search procedure conclude.

   Concretely, the game checks that the oracles `accA` and `unblind`
   are called on identical arguments `sA` using the log `logA` and
   inclusion checks `logA ⊆ sA` in both oracles.
   (a similar check is used for the argument `sB` of the oracles
   `accB` and `unblind` *)
game AdaptativeSelectiveFailureBlindness = {
  rnd token0 : token_bsign;
  rnd token1 : token_bsign;

  let m0 = #init;
  let m1 = #init;
  let pk = #init;

  var logA = empty_set;
  var logB = empty_set;


  oracle blindingA = {
    return blind diff(m0,m1) pk token0;
  }

  oracle accA sA = { 
    var logA' = logA;
    var sAm = format sA;
    logA := add sAm logA;
    return 
      if subseteq logA' (singleton sAm) then
        baccepte diff(m0,m1) pk token0 sA
      else witness
  }

  oracle blindingB = {
    return blind diff(m1,m0) pk token1;
  }

  oracle accB sB = {
    var logB' = logB;
    var sBm = format sB;
    logB := add sBm logB;
    return 
      if subseteq logB' (singleton sBm) then
        baccepte diff(m1,m0) pk token1 sB 
      else witness
  }

  oracle unblind (sA,sB : bsigned) = {
    var logA' = logA;
    var logB' = logB;

    var sAm = format sA;
    var sBm = format sB;

    var accA = baccepte diff(m0,m1) pk token0 sA;
    var accB = baccepte diff(m1,m0) pk token1 sB;
    var ub0 = unblind m0 pk diff(token0,token1) diff(sA,sB);
    var ub1 = unblind m1 pk diff(token1,token0) diff(sB,sA);

    logA := add sAm logA;
    logB := add sBm logB;

    return 
      if subseteq logA' (singleton sAm) &&
         subseteq logB' (singleton sBm) then
        if accA && accB 
        then (ub0, ub1)
        else witness
      else witness
    }
}.

(*------------------------------------------------------------------*)
(* Commitment Hiding 
   Moni Naor:
   Bit Commitment Using Pseudorandomness. J. Cryptol. 4(2): 151-158 (1991) 

   Boneh, Shoup:
   A Graduate Course in Applied Cryptography, 2023
*)

game CommitmentHiding = {
  oracle challenge (m0,m1 : message) = {
    rnd key : k_comm;
    return comm diff(m0,m1) key;
  }
}.


(* Commitment Key Hiding property. Trivially follows from the
   Commitment Hiding property, as an adversary that can compute the
   commitment key can open the left-right challenge in the Commitment
   Hiding game to distinguish the left from right scenarios. *)
game CommitmentKeyHiding = {
  rnd key : k_comm;

  let commited_message = #init;

  oracle commit = {
    return comm commited_message key;
  }

  oracle challenge (guess : k_comm) = {
    return diff(key = guess,false);
  }
}.

(*------------------------------------------------------------------*)
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
    return if (len m0) = (len m1) then encr diff(m0,m1) (pk_enc key) seed else witness
  }
  oracle decrypt (c : ctxt) = {
    return if not (mem (format c) log) then decr c key
  }
}.
