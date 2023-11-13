(* Variant of `examples/private-authentication.sp` where cryptographic game
   CPA_$ replaces the CCA1 and ENC-KP assumptions. *)

(**
# PRIVATE AUTHENTICATION

The Private Authentication protocol as described in [F] involves an initiator A
and a responder B.

The initiator A sends a message `enc(<pkA,n0>,r0,pkB)` to the responder B,
where `pkA` (respectively `pkB`) is the public key of A (respectively B).
The responder B checks that the first projection of the decryption of the
received message is equal to `pkA` and that the second projection of the
decryption of the received message has a correct length.
In that case, B sends back `enc(<n0,n>,r,pkA)`.

The protocol is as follows:

* A -> B : enc(<pkA,n0>,r0,pkB)
* B -> A : enc(<n0,n>,r,pkA)

This is a "light" model without the last check of A.

In this file we prove that an attacker can't tell whether B is willing
to communication with A or some other agent Abis. We use the CCA$
cryptographic assumption instead of CCA1.

[F] G. Bana and H. Comon-Lundh. A computationally complete symbolic
attacker for equivalence properties. In 2014 ACM Conference on
Computer and Communications Security, CCS ’14, pages 609–620.
ACM, 2014

******************************************************************************
*)

include Basic.

(* We assume a type `ptxt` for plain-text messages, of bounded length.
   This is achieved by taking a truncation function from messages
   to plain-texts. We don't need any explicit axiom on this function. *)
type ptxt[large].
abstract truncate : message -> ptxt.

(* Cryptographic primitives. We use custom projection functions rather
   than the built-ins, because the implementation does not yet take
   into account the fact that these are PTIME computable. *)
abstract enc : (ptxt * ptxt) -> message -> message -> message
abstract dec : message -> message -> (ptxt * ptxt)
abstract pk : message -> message.
abstract fst_ptxt : ptxt * ptxt -> ptxt.
abstract snd_ptxt : ptxt * ptxt -> ptxt.

game CPASAMP = {
  rnd key : message;
  oracle pk = {
    return pk(key)
  }
  oracle challenge (m:ptxt*ptxt) = {
    rnd r:message;
    rnd dummy : message;
    return diff (enc m r (pk key), dummy)
  }
}.

(* ------------------------------------------------------------------ *)

(* Protocol *)

(* Secret keys for the three roles. *)
name kA    : message
name kAbis : message
name kB    : message.

(* Nonces for the three roles. *)
name n0 : index -> ptxt
name n0bis : index -> ptxt
name n : index -> ptxt.

(* Randomization for encryptions. *)
name r : index -> message
name r0 : index -> message
name r0bis : index -> message.

(* Channels for all roles. *)
channel cA
channel cAbis
channel cB
channel cO.

process A(i:index) =
  out(cA,    enc (truncate (pk kA   ), n0    i) (r0    i) (pk kB)).

process Abis(i:index) =
  out(cAbis, enc (truncate (pk kAbis), n0bis i) (r0bis i) (pk kB)).

(* Role B, talking to A in left system and Abis in right system. *)
process B(j:index) =
  in(cB, mess);
  let dmess : ptxt*ptxt = dec mess kB in
  out(cB,
    enc
      (if fst_ptxt dmess = truncate diff(pk(kA),pk(kAbis))
       then (snd_ptxt dmess, n j)
       else (n j, n j))
      (r j)
      (pk (diff (kA,kAbis)))).

system O:
  out(cO,<<pk(kA),pk(kAbis)>,pk(kB)>);
  (!_i A(i) | !_ibis Abis(ibis) | !_j B(j)).

(* ------------------------------------------------------------------ *)

(* Proof of anonymity *)

name dummy : message.

global lemma anonymity (tau:timestamp[const]) : [happens(tau)] -> equiv(frame@tau).
Proof.
  intro _.
  enrich pk(kA), pk(kB), pk(kAbis).
  induction tau.
  + auto.
  + (* Output of public keys. *)
    expandall. 
    fa 3. auto. 
  + (* A *)
    expandall.
    fa !<_,_>, if _ then _.
    fa (enc _ _ _), (truncate _, n0 i).
    fresh 5; 1:auto.
    by fresh 4.
  + (* Abis *)
    expandall.
    fa !<_,_>, if _ then _.
    fa (enc _ _ _), (truncate _, n0bis ibis).
    fresh 5; 1:auto.
    by fresh 4.
  + (* B *)
    expand frame, output, exec, cond, dmess.
    fa !<_,_>, if _ then _.
    trans 4 : dummy; 1 : sym;trans 4 : dummy.
    * by fresh 4.
    * sym; by crypto CPASAMP (key : kA).
    * sym; by crypto CPASAMP (key : kAbis).
Qed.
