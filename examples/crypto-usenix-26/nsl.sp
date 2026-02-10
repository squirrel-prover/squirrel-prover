(** Needham-Schroeder-Lowe protocol.*)

(** This file is an improved version of the NSL development included
    in the artifacts for the CCS 2024 paper by Baelde, Koutsos & Sauvage,
    "Foundations for Cryptographic Reductions in CCSA Logics". This artifact
    is available at <https://theses.hal.science/INRIA2/hal-04650670v1>
    and the individual file is also visible at
    <https://github.com/squirrel-prover/squirrel-prover/blob/master/examples/crypto/nsl.sp>.

    In the original file, the crypto tactic is used to prove simplified
    equivalences between variants of the main messages. The involved terms
    contain no macros. Then, a manual bi-deduction proof (without crypto)
    is performed to derive the equivalences between frames from these core 
    equivalences. That approach, resulting in hundreds of lines of tactics,
    was necessary because of the systematic shortcomings of the initial 
    implementation of crypto with the CCA2 game, as explained in our paper.
    To work around this issue, crypto is used on the CCA2 game on a goal
    where inductive bi-deduction is not required, and induction is then
    performed by hand. Our new implementation of crypto, which synthesizes
    memoizing simulators and the associated time-sensitive invariants, can
    directly prove the equivalences on frames, resulting in an immediate,
    fully-automatic proof. *)

(** The NSL protocol describes the interaction between two participants,
    Alice (`A`) and Bob (`B`),
    who want to exchange their respective secret random data `nA` and `nB`
    without them beeing revealed to an active attacker.
    It relies on a CCA2 encryption to achieve both secrecy and authentication.

    Each participant has its own secret encryption key and the two
    associated public keys `pkA` and `pkB` are distributed prior to
    the exchange, which is as follows:
 
```
    A -> B: {nA,pkA}_pkB
    B -> A: {nA,nB,pkB}_pkA
    A -> B: {nB,nA}_pkB
```

    In this file we prove that a simple scenario of this protocol
    is indistinguishable from a variant where encrypted messages
    are replaced by their length (in unary), relying on the
    IND-CCA2 crypto assumption. We explain how this is useful to
    prove the strong secrecy of the exchanged nonces `nA` and `nB`.

    We consider a single session of each participant. The initiator
    `A` uses a public key that is chosen by the attacker, allowing
    man in the middle attacks.
    We assume a tagging mechanism to distinguish the first and last
    messages from `A`. *)

include Core.

(* ------------------------------------------------------------------------ *)

(** Constructors and destructors for contents of the three messages.
    This amounts to minimal assumptions on how messages are formatted,
    but we make further assumptions about lengths and tags below. *)

abstract make1 : message * message -> message.
abstract get1_na : message -> message.
abstract get1_id : message -> message.
axiom [any] get1_na  (x,y:_) : get1_na(make1(x,y)) = x.

abstract make2 : message * message * message -> message.
abstract get2_na : message -> message.
abstract get2_nb : message -> message.
abstract get2_id : message -> message.
axiom [any] get2_na (x,y,z:_) : get2_na(make2(x,y,z)) = x.
axiom [any] get2_nb (x,y,z:_) : get2_nb(make2(x,y,z)) = y.
axiom [any] get2_id (x,y,z:_) : get2_id(make2(x,y,z)) = z.

abstract make3 : message * message -> message.
abstract get3_na : message -> message.
abstract get3_nb : message -> message.
axiom [any] get3_na (x,y:_) : get3_na(make3(x,y)) = x.
axiom [any] get3_nb (x,y:_) : get3_nb(make3(x,y)) = y.

(* ------------------------------------------------------------------------ *)

(** Asymmetric encryption and CCA2 game. *)

(** We rely on encryption and decryption functions such that,
    for any plaintext `m`, encryption key `k` and encryption randomness `r`,
    `dec (enc m k r) k = m`.
 
    We assume that encryption is secure against chosen-ciphertext
    attacks in the sense of the IND-CCA2 game.
    The game expresses the indistinguishability between
    two encrypted messages of same length.
    The adversary is given access to a challenge oracle `encrypt`
    that takes two inputs `m0`,`m1` and (provided they have the same length)
    returns:

    - in the left-game the encryption of `m0` and
    - in the right-game the encryption of `m1`.

    Moreover the adversary can also use a decryption oracle
    on any message other than the ones outputted by the `encrypt`
    oracle. *)

abstract pub : message -> message.
abstract dec : message*message -> message.
abstract enc : message*message*message -> message.

game CCA2 = {
  rnd key : message;
  var log = empty_set;
  oracle pk = {
    return (pub key)
  }
  oracle encrypt (m0,m1 : message) = {
    rnd r: message;
    var c = enc(diff(m0,m1),r,pub key);
    log := add c log ;
    return if zeroes m0 = zeroes m1 then c else empty
  }
  oracle decrypt (c : message) = {
    return if not (mem c log) then dec(c,key)
  }
}.

(* ------------------------------------------------------------------------ *)

(** Protocol description.
    We consider only one session of each role. *)

name ska : message.
name skb : message.

name na  : message.
name nb  : message.
name r1  : message.
name r1' : message.
name r2  : message.
name r2' : message.
name r3  : message.
name r3' : message.

(* Introduce three constants that are assumed to have the same
   lengths, respectively, as the three messages.
   We also assume that len1 passes the tag verification associated
   to the first message, but that len3 and make3 results do not. *)
abstract len1 : message.
abstract len2 : message.
abstract len3 : message.

axiom [any] len1 : zeroes len1 = zeroes(make1(na,pub(ska))).
axiom [any] len2 : zeroes len2 = zeroes(make2(na,nb,pub(skb))).
axiom [any] len3 : zeroes len3 = zeroes(make3(nb,na)).
hint smt len1.
hint smt len2.
hint smt len3.

abstract check_tag1 : message -> bool.
axiom [any] check_tag1_msg1 (x,y:message) : check_tag1 (make1(x,y)).
axiom [any] check_tag1_msg3 (x,y:message) : not (check_tag1 (make3(x,y))).
axiom [any] check_tag1_len1 : check_tag1 len1.
axiom [any] check_tag1_len3 : not (check_tag1 len3).

channel c.

set processStrictLetMode = true.

(** We define our main bi-system:

    - NSL/left is the real protocol;
    - NSL/right is the idealized protocol where the contents of encryptions
      are changed by zeroes.

    Note that NSL/left already "anticipates" the idealization by incorporating
    special cases in its logic (e.g. Bob outputs msg2 when msg1 is received)
    but this is obviously equivalent to the original specification (modulo
    axioms on tag verifications). *)

process Alice =
  let a_msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub skb) in
  let a_msg2 = enc(diff(make2(na,nb,pub skb),len2),r2,pub ska) in
  let a_msg3 = enc(diff(make3(nb,na),len3),r3,pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then a_msg1 else enc(make1(na,pub ska),r1',pk));
  in(c,x);
  (* Last output of Alice, to which we add <na,nb> to model strong secrecy
     when the protocol completes and pk is honest, i.e. pk = pub skb. *)
  out(c, (* Cannot decrypt msg2: express result directly. *)
         if x = a_msg2 then (if pk = pub skb then <a_msg3,<na,nb>>) else
         if get2_na(dec(x,ska)) = na && get2_id(dec(x,ska)) = pk then
         (* Use alternative randomness for encryption. *)
         <enc(make3(get2_nb(dec(x,ska)),na), r3', pk),
          if pk = pub skb then <na,nb>>).

process Bob =
  let b_msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub skb) in
  let b_msg2 = enc(diff(make2(na, nb, pub skb),len2),r2,pub ska) in
  let b_msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  in(c,x);
  out(c, (* Cannot decrypt msg1: express result directly. *)
         if x = b_msg1 then b_msg2 else
         (* Cannot decrypt msg3: directly encode result (failed tag check). *)
         if x = b_msg3 then empty else
         if check_tag1 (dec(x,skb)) then
         enc(make2(get1_na(dec(x,skb)),
                   nb, pub skb),
             r2', get1_id(dec(x,skb)))).

system NSL =
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice)|(B : Bob))).

(** We now explain why observational equivalence of NSL/left and /right
    implies the strong secrecy of na and nb: the output of these
    two nonces at the end of Alice can be replaced by two fresh names
    without the attacker being able to distinguish the two situations.
 
    Note that, in NSL/right, if we exclude the final output of `<na,nb>`:

    - assuming `pk = pub skb`,
      `na` only occurs in the last test and encryption of Alice;
    - `nb` only occurs in the last encryption of Bob.
 
    We could then prove, when `pk = pub skb`, that
    `get2_na(dec(input@A1,ska)) = na` is always false by freshness of `na`
    at this point. This allows to prove that the final output of `na`
    is indistinguishable from a fresh name (it is actually a fresh name itself):
    thus `na` is strongly secret in NSL/right. By observational equivalence,
    it is also strongly secret in the real protocol NSL/left.
 
    Further, we only output `<na,nb>` at the end of Alice if `pk = pub skb`
    and the execution is successful:
      `input@A1 = msg2 || get2_na(dec(input@A1,ska)) = na`.
    We've seen that the second part is always false. Now, `input@A1 = msg2`
    can only hold if Bob sent that message (by IND-CCA2) hence `input@B = msg1`.
    Under our condition, we thus have no occurrence of `nb` on Bob's side,
    hence `nb` is also indistinguishable from a fresh name in the final output
    of `<na,nb>` by Alice. *)

(** It would also be good to model the strong secrecy of `nb` when Bob
    believes he's had a honest interaction with Alice -- this property fails in
    the original Needham-Schroeder protocol due to the man-in-the-middle attack.
    This would be modelled by outputting `nb` at the end of Bob's process when
    `get1_id(dec(input@B,skb)) = pub ska`. However, proving that this output
    is indistinguishable from a fresh name requires idealizing further the
    process, and introduce extra difficulties on Alice's side: we leave this
    more complete proof to future work, but note that these aspects are
    independent of CCA2 reasoning and bi-deduction. *)

(* ----------------------------------------------------------------------- *)

(** Because we apply CCA2 for each key ska and skb separately,
    we need to introduce an intermediate (bi)system:

    - NSL_a/left has real messages for outputs of Alice,
      but idealized ones for Bob's messages;
    - NSL_a/right is the same as NSL/right. *)

process Alice_a =
  let a_msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub(skb)) in
  let a_msg2 = enc(len2,r2, pub ska) in
  let a_msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  in(c,pk);
  out(c, if pk = pub skb then a_msg1 else enc(make1(na,pub ska),r1',pk));
  in(c,x);
  out(c, if x = a_msg2 then (if pk = pub skb then <a_msg3,<na,nb>>) else
         if get2_na(dec(x,ska)) = na && get2_id(dec(x,ska)) = pk then
         <enc(make3(get2_nb(dec(x,ska)),na), r3', pk),
          if pk = pub skb then <na,nb>>).

process Bob_a =
  let b_msg1 = enc(diff(make1(na,pub(ska)),len1),r1,pub(skb)) in
  let b_msg2 = enc(len2,r2,pub ska) in
  let b_msg3 = enc(diff(make3(nb,na), len3), r3, pub skb) in
  in(c,x);
  out(c, if x = b_msg1 then b_msg2 else
         if x = b_msg3 then empty else
         if check_tag1 (dec(x,skb)) then
         enc(make2(get1_na(dec(x,skb)),
                   nb, pub skb),
             r2', get1_id(dec(x,skb)))).

system NSL_a =
  (PUB : out(c, <pub(ska),pub(skb)>);
  ((A : Alice_a)|(B : Bob_a))).

(* ----------------------------------------------------------------------- *)

(** Proofs *)

(* Observational equivalence
   between NSL_a/left and NSL/right (= NSL_a/right). *)
global lemma [NSL_a/left,NSL/right] equiv_right (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  crypto CCA2 (key:skb); project; smt.
Qed.

(* Observational equivalence between NSL/left and NSL_a/left. *)
global lemma [NSL/left,NSL_a/left] equiv_left (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  crypto CCA2 (key:ska); project; smt.
Qed.

(* ------------------------------------------------------------------------ *)

(* We finally prove that the two projections of the bi-system NSL
   are observationally equivalent, by transitivity. *)

(* Immediate consequence of equiv_left. *)
global lemma
  [set: NSL; equiv:NSL/left,NSL_a/left]
  equiv_left_sys (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  trans [NSL/left,NSL_a/left].
  + auto.
  + by apply equiv_left.
  + auto.
Qed.

(* Immediate consequence of equiv_right. *)
global lemma
  [set:NSL; equiv:NSL_a/left,NSL/right]
  equiv_right_sys (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  trans [NSL_a/left,NSL/right].
  + auto.
  + by apply equiv_right.
  + auto.
Qed.

global theorem [NSL] nsl_security (t:timestamp[const]) :
  [happens(t)] -> equiv(frame@t).
Proof.
  intro *.
  trans [NSL_a/left,NSL_a/left].
  + by apply equiv_left_sys.
  + auto.
  + by apply equiv_right_sys.
Qed.
