(*****************************************************************************

This is a toy example illustrating how one can use an IND-CCA asymmetric
encryption to build a key-exchange, in a very basic threat model with a single
session.

# Protocol description

We consider two parties I (initiator) and R (responder).
They both exchange fresh nonces kI and kR, encrypted using the other party's
public key, and then derive a shared secret h(s,kI2) XOR h(s,kR2),
where h is a PRF hash function and s a public seed.

Static keys for party X : skX.
Public keys for party X : pkX = pk(skX).

```
------------------------------+----------------------------------
         Initiator            |        Responder
------------------------------+----------------------------------
  new kI;                     |  new kR;
  ctI := Encap(kI, rI, pkR)   |  ctR := Encap(kR, rR, pkI)
                              |
                       I  --(ctI)-> R
                       I <--(ctR)-- R
                              |
  kR2 := Decap(ctR,dkI)       |  kI2 := Decap(ctI,dkI)
------------------------------+----------------------------------
```

Final key derivation: KIR := h(s,kI2) XOR h(s,kR2).

******************************************************************************)

include Basic.

(***********************)
(* Global Declarations *)
(***********************)

(* Enable post-quantum checks so that results are post-quantum sound. *)
set postQuantumSound = true.

(* Declare a hash function h, that is assumed to be a prf. *)
hash h.

(* Declare a public random name (nonce) for the key derivations with h. *)
name s : message.

(* Declare an asymmetric encryption assumed to be IND-CCA2. *)
aenc enc,dec,pk.

(* Long term keys of I and R. *)
name skI :  message.
name skR : message.

(* Session names. *)
name kI : message.
name rI : message.
name kR : message.
name rR : message.

(* Cells used to stored the derived keys. *)
mutable sIR : message =  zero.
mutable sRI : message =  zero.

(* Communication channels. *)
channel cI.
channel cR.

(* Squirrel currently doesn't allow a flexible modelling of the length
   of hashes. The PRF assumption implicitly assumes that hashes are
   of length namelength_message (aka the security parameter eta) which
   we also need to make explicit here. *)
axiom [any] len_h (x,y:message) : len(h(x,y)) = namelength_message.

(******************)
(* Protocol Model *)
(******************)

process Initiator =
  (* Fresh ephemeral secret share. *)
  (* Fresh randomness for the encryption. *)
  (* Send kI encrypted for R. *)
  out(cI, enc(kI,rI,pk(skR)) );
  (* Receive some encrypted share. *)
  in(cR,ctR);
  (* Decrypt it. *)
  let kR = dec(ctR,skI) in
  (* Combine kI and kR in a key. *)
  sIR :=  h(s,kI) XOR h(s,kR).

process Responder =
  in(cI, ctI);
  out(cR, enc(kR, rR, pk(skI))).
  (* We omit the Responder key derivation for simplicity. *)

(* Finally declare our "real" system, where the public seed
   s is disclosed, after which our two agents run in parallel. *)
system [real] out(cI,s); (Responder | Initiator).

(**********************)
(* Idealized Protocol *)
(**********************)

(* Variant of the protocol where kfresh replaces kI in the first message.
   This will lead to our "ideal" system. We will prove, using the CCA1
   assumption, that the two systems are equivalent in a strong sense.
   This will allow us to prove strong secrecy for the ideal system and
   then transfer the result to the real system. *)

name kfresh: message.

process InitiatorCCA =
  out(cI,enc(kfresh,rI,pk(skR)));
  in(cR,ctR);
  let kR = dec(ctR,skI) in
  sIR := h(s,kI) XOR h(s,kR).

system [ideal] out(cI,s); (Responder | InitiatorCCA).

(* Note that both of our systems are bi-systems with equal projections.
   This could be improved when Squirrel allows the declaration of single
   systems. It could also be avoided by declaring a bi-system whose
   projections would correspond to the ideal and real systems. *)

(**********)
(* Proofs *)
(**********)

(* Technical lemma about lengths. *)
lemma [real/left,ideal/left] lengths :
  len(diff(kI,kfresh)) = namelength_message.
Proof.
  project. by rewrite namelength_kI. by rewrite namelength_kfresh.
Qed.

(* Equivalence between the real and ideal systems,
   with some extra messages given to the distinguisher. *)
global lemma [set: real/left; equiv: real/left, ideal/left] ideal_real :
  Forall (tau:timestamp[const]),
  [happens(tau)] -> equiv(frame@tau, pk(skR), pk(skI), kI, s, skI).
Proof.
  intro tau; induction tau => Htau.
  + (* tau = init *)
    auto.
  + (* tau = A *)
    by expandall; apply IH.
  + (* tau = Responder *)
    expandall. fa !<_,_>, (if _ then _), enc _.
    fresh 1 => //. (* kR *)
    fresh 1 => //. (* rR *)
    by apply IH.
  + (* tau = Initiator *)
    expandall. fa !<_,_>, if _ then _.
    cca1 1 => //.
    fa enc _.
    rewrite lengths.
    fresh 1 => //. (* rI *)
    apply IH => //.
  + (* tau = Initiator1 *)
    by expandall; apply IH.
Qed.

(* Strong secrecy for the ideal system,
   expressed using a fresh ideal key ikIR. *)
name ikIR : message.
global lemma [ideal/left, ideal/left] strong_ideal (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,if tau = Initiator1 then diff(sIR@tau,ikIR)).
Proof.
  induction tau => Hap; try by rewrite if_false.
  (* tau = Initiator1 *)
  simpl. rewrite /sIR.
  prf 1, h(s,kI).
  xor 1.
  rewrite if_true.
  + by rewrite len_h namelength_n_PRF.
  + by fresh 1.
Qed.

(* Technical lemma. *)
lemma [real/left, ideal/left] diff_refl (x:message) : diff(x,x) = x.
Proof.
  by project.
Qed.

(* The final strong secrecy result is the consequence of the previous
   lemmas by transitivity. *)
global lemma [set: real/left;
             equiv: real/left,real/left] SSec_real (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,if tau = Initiator1 then diff(sIR@tau,ikIR)).
Proof.
  intro Hap.
  trans [ideal/left,ideal/left].

  * (* First equivalence: real versus ideal with sIR. *)
    rewrite /sIR /kR1 /kR2.
    rewrite diff_refl.
    by apply ideal_real.

  * (* Second equivalence: strong secrecy on ideal system.  *)
    by apply strong_ideal.

  * (* Third equivalence: ideal versus real with ikIR. *)
    fa 1; fresh 2 => //.
    by apply ideal_real.
Qed.
