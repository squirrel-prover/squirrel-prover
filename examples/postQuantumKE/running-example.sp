(*******************************************************************************

This is a toy example illustrating how one can use an IND-CCA asymmetric encryption to
build a key-exchange, in a very basic threat model with a single session.

# Protocol description We consider two parties I (initiator) and R (responder).
 They both exchange fresh nonces kI and kR, encrypted using the
other party public key, and then derive a shared secret h(s,kI2) XOR h(s,kR2),
where h is a PRF hash function and s a public seed.  and derive from them a
secret using a kdf and xor.


Static keys for party X := skX
Public keys for party X : pkX = pk(skX)

Initiator                                  Responder
new kI;
ctI := Encap(kI, rI  ,pk(skR))

                      --(pkI,ctI)->


                                         new kR;
                                         ctR := Encap(kR, rR , pkI)
                   I <--(R,ctR)-- R



kR := Decap(ctR,dkI)

                                         kI := Decap(ctI,dkI)

Final key deriviation:
KIR := h(s,kI2) XOR h(s,kR2)


*******************************************************************************)

include Basic.

(***********************)
(* Global Declarations *)
(***********************)

(* We first enable the postQuantum checks. *)
set postQuantumSound = true.

(* This line declares a hash function h, that is assumed to be a prf. *)
hash h

(* We declare a public random name (nonce) for the key derivations with h *)
name s : message

(* We declare an assymetric encryption assumed to be IND-CCA2*)
aenc enc,dec,pk

(* Long term key of I *)
name skI :  message

(* Long term key of R *)
name skR :  message

(* Cells used to stored the derived key *)
mutable sIR: message =  zero
mutable sRI: message =  zero

channel cI
channel cR.

(********************************)
(* Protocol Agents Declarations *)
(********************************)

process Initiator =
 (* Fresh ephemeral secret share. *)
 new kI;
 (* Fresh randomness for the encryption. *)
 new rI;
 (* Send kI encrypted for R *)
 out(cI,  enc(kI, rI,pk(skR)) );
 (* Receive some encrypted share. *)
 in(cR,ctR);
 (* Decrypt it. *)
 let kR = dec(ctR,skI) in
 (* And combine kI and kR in a key. *)
 sIR :=  h(s,kI) XOR h(s,kR).

process Responder =
   new kR;
   new rR;
   in(cI, ctI);
   out(cR, enc(kR, rR, pk(skI))).
   (* We omit the Responder key derivation for simplicity *)

(* We finally declare the protocol model. *)
system [main] out(cI,s); (Responder | Initiator).


(* As a first proof step, we first apply globally CCA to hide kR from the
attacker, this yield a new system mainCCAkr that we know to be equivalent from
the previous one. *)
system mainCCAkR = [main/left] with gcca, enc(kI, rI,
pk(skR)).

(*******************************************)
(*** Strong Secrecy of the derived key ***)
(*******************************************)

(* We  define a fresh ideal key. *)
name ikIR : message.

(* And we must assume that hashes are of the same length as the expected length of secret keys.  *)
axiom  [mainCCAkR] len_hashes (x1,x2:message) : len(h(x1,x2)) = len(s).
(* And we prove that whenever the initiator terminates, which correspond to
action Initiator1, the key stored in the state sIR@Initiator1 is
indistinguishable from ikIR.  Remark that this holds even if the encryption
received by the initiator is dishonnest, because the attacker cannot compute kI.
 *)
global goal [mainCCAkR, mainCCAkR] resp_key: [happens(Initiator1)] -> equiv(frame@Initiator1, diff(sIR@Initiator1, ikIR)).
Proof.
  intro Hap .

  (* We expand all the macros. *)
  expandall.
  (* This action has a trivial output, so we can simplify it with function applications *)
  fa 0.

  (* We apply the prf assumption. *)
  prf 1, h(s,kI).
  (* The condition for the validity of the PRF application is trivial, as kI is
  hidden from the attacker through the CCA application. *) (* We thus simplify the
  trivial conditional. *) 
  rewrite if_true // in 1.
  (* We now use the one-time pad property of the xor. *)
  xor 1.
  (* We show that the condition of the introduced conditional is always true. *)
  rewrite if_true in 1.
  (* First by using the axiom saying that the length of the hash output is equal
  to the length of the public name s. *)
  rewrite len_hashes.
  (* Then using the assumption that all names of the same length. *)
  by namelength s,n_PRF.

  (* Finally, we have to prove that two completely fresh names are
  indistinguishable. This is done with the fresh tactic. *)
  fresh 1; 1:auto.

  (* We only have left to prove that before the computation of the key, the
  protocol was indistinguishable, which is trivial because it did not contain any
  diff operations. *)
  diffeq => *.
Qed.
