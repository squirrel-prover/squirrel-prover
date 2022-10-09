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
(* set postQuantumSound = true. *)

(* This line declares a hash function h, that is assumed to be a prf. *)
hash h
abstract name_length: message

(* We declare a public random name (nonce) for the key derivations with h *)
name s : message

(* We declare an assymetric encryption assumed to be IND-CCA2*)
aenc enc,dec,pk

(* Long term key of I *)
name skI :  message

(* Long term key of R *)
name skR :  message
name n: message

name kI: message.
name rI:message.
name nI: message.
name nR:message.

name kR: message.
name rR:message.

name nfresh:message.
(* Cells used to stored the derived key *)
mutable sIR: message =  zero.
mutable sRI: message =  zero

channel cI
channel cR.

(********************************)
(* Protocol Agents Declarations *)
(********************************)

process Initiator =
 (* Fresh ephemeral secret share. *)
 (* Fresh randomness for the encryption. *)
 (* Send kI encrypted for R *)
 out(cI,  enc(kI, rI,pk(skR)) );
 (* Receive some encrypted share. *)
 in(cR,ctR);
 (* Decrypt it. *)
 let kR = dec(ctR,skI) in
 (* And combine kI and kR in a key. *)
 sIR :=  h(s,kI) XOR h(s,kR).

process Responder =
   in(cI, ctI);
   out(cR, enc(kR, rR, pk(skI))).
   (* We omit the Responder key derivation for simplicity *)

(* We finally declare the protocol model. *)
system [main] out(cI,s); (Responder | Initiator).


name kfresh: message.

process InitiatorCCAkR = 
out(cI,enc(kfresh, rI,pk(skR)));
in(cR,ctR);
let kR = dec(ctR,skI) in
sIR := h(s,kI) XOR h(s,kR).


system [mainCCAkR]  out(cI,s); (Responder | InitiatorCCAkR).


(* HELP: Je voulais dire que la longueur des noms etait fixe. Cet axiome est donc trop fort *)  
axiom  [main/left,mainCCAkR/left] len(x1:message) : len(x1) = name_length.

global goal [main/left, mainCCAkR/left] ideal_real (tau:timestamp) : 
    [happens(tau)]-> equiv(frame@tau, pk(skR), pk(skI), kI, s, skI).

Proof.

induction tau => Htau.

(* t = init *)
expandall.auto.
(* t= A *)
expandall. fa !<_,_>. apply IH => //.
(* t = Responder *)
expandall. fa !<_,_>. fa 1. fa 1. fresh 1. rewrite if_true => //.
fresh 1. rewrite if_true => //.
apply IH => //.
(* t = Initiator *)
expandall. fa !<_,_>. fa 1. cca1 1. assert (len(diff(kI,kfresh)) = diff(len(kI),len(kfresh))). admit.
rewrite H.
use len with kI.
use len with kfresh.
rewrite H0. rewrite H1. 
apply IH => //. auto.
(* t = Initiator1 *)
expandall. fa !<_,_>.  apply IH => //.
Qed.



(* We  define a fresh ideal key. *)
name ikIR : message.
axiom  [mainCCAkR] len_hashes (x1,x2:message) : len(h(x1,x2)) = len(s).

global goal [mainCCAkR/left, mainCCAkR/right] strong_ideal (tau:timestamp) :
  [happens(tau)]-> equiv(frame@tau,if tau = Initiator1 then diff(sIR@tau,ikIR)).

Proof.
induction tau => Hap. 

(* t= init *)
expandall. rewrite if_false => //.
(* t = A *)
expandall. fa !<_,_>. fa 1.
rewrite if_false  => //. fresh 1. rewrite if_true => //.
apply IH => //.
(* t= Responder *)
expandall. fa !<_,_>. fa 1. 
rewrite if_false  => //.
fa 1. fa 3. fresh 1 => //; rewrite if_true => //.
fresh 1 => //. rewrite if_true => //.
fresh 1 => //. rewrite if_true => //.
apply IH => //.
(* t = Initiator *)
expandall. fa !<_,_>. fa 1. 
rewrite if_false  => //. fa 1.
 fa 3.
fresh 1 => //. rewrite if_true => //.
fresh 1 => //. rewrite if_true => //.
fresh 1 => //. rewrite if_true => //.
apply IH => //.
(* t = Initiator1 *)
expandall. fa !<_,_>.
rewrite if_true => //.
prf 1, h(s,kI).
rewrite if_true => //.
xor 1. 
rewrite if_true.
  rewrite len_hashes.
  (* Then using the assumption that all names of the same length. *)
  by namelength s,n_PRF.
fresh 1.
apply IH => //.
Qed.

