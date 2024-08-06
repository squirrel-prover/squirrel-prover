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

In this file, we prove anonymity, _i.e._ that an attacker cannot tell whether
a session is initiated by an identity A or by an identity Abis.

[F] G. Bana and H. Comon-Lundh. A computationally complete symbolic
attacker for equivalence properties. In 2014 ACM Conference on
Computer and Communications Security, CCS ’14, pages 609–620.
ACM, 2014

******************************************************************************
*)

include Core.

(**
We first declare the communication channels, the function symbols for the public
encryption scheme as well as the several names used in the protocol's messages.
*)

channel cA
channel cAbis
channel cB
channel cO

aenc enc,dec,pk

name kA    : message
name kAbis : message
name kB : message

name n0 : index -> message
name r0 : index -> message
name n0bis : index -> message
name r0bis : index -> message

name n : index -> message
name r : index -> message.

(**
We also declare a public function symbol `plus`, which we will use to model
the addition of lengths of messages.
*)

abstract (++) : message -> message -> message.


game Enckp = {
 rnd k0:message;
 rnd k1:message;

 oracle pk0 = {return pk(k0)}
 oracle pk1 = {return pk(k1)}
 oracle challenge x = {
   rnd r:message;
   return enc(x,r,pk(diff(k0,k1)))
 }
}



(**
The initiator A is indexed by `i` to represent an unbounded number of sessions
and is defined by a single output.
*)
process A(i:index) =
  out(cA, enc(<pk(kA),n0(i)>,r0(i),pk(kB))).

(**
We define a similar process for the initiator Abis.
*)
process Abis(i:index) =
  out(cAbis, enc(<pk(kAbis),n0bis(i)>,r0bis(i),pk(kB))).

(**
The responder B is indexed by `j` to represent an unbounded number of sessions.

In order to express anonymity using an equivalence property, we model two
systems using the `diff` operator.
On the left side, the key `kA` is used while the right side uses the key `kAbis`.
*)
process B(j:index) =
  in(cB, mess);
  let dmess = dec(mess, kB) in
  out(cB,
    enc(
      (if fst(dmess) = diff(pk(kA),pk(kAbis)) && len(snd(dmess)) = len(n(j)) then
         <snd(dmess), n(j)>
       else
         <n(j), n(j)>),
      r(j), pk(diff(kA,kAbis)))
  ).

(**
The protocol is finally defined by a system where an unbounded number of
sessions for A, Abis and B play in parallel, after having outputted the
public keys of A, Abis and B.
*)
system O:
  out(cO,<<pk(kA),pk(kAbis)>,pk(kB)>);
  (!_i A(i) | !_ibis Abis(ibis) | !_j B(j)).

(**
This axiom states that the length of a pair is equal to the sum of the lengths
of each component of the pair.
*)

axiom length_pair (m1:message, m2:message): len(<m1,m2>) = len(m1) ++ len(m2).


(* Helper lemma *)
lemma if_same_len (x,y : message, b : boolean):
  (b => (len x = len y)) =>
  (len (if b then x else y) = len y).
Proof.
  by intro *; case b.
Qed.

(* Helper lemma (f_apply twice does not work, 
as f a and f aa are not the same) *)
lemma f_apply2 ['a 'b 'c] (f:'a -> 'b -> 'c) (a,aa:'a) (b,bb:'b) :
 a = aa =>
 b = bb => 
 f a b = f aa bb.
Proof.
 intro ->. by intro ->.
Qed. 


(**
The anonymity property is expressed as an equivalence between the left side
(the one using `kA` and the right side (the one using `kAbis`) of the system.
This property is expressed by the logic formula `forall t:timestamp, frame@t`
where `frame@t` is a bi-frame.
*)
equiv anonymity.
(**
The high-level idea of the proof is as follows: we show that the message
outputted by the role B does not give any element to the attacker
to distinguish the left side from the right side, relying on the fact that
encryption satisfies key privacy and IND-CCA1 assumptions.
*)
Proof.

  (**
  We start by adding to the frame the two public keys `pk(kA)`, `pk(kAbis)`
  and `pk(kB)` since any execution starts by the action `O` outputting them.
  This allows to simplify some cases in the proof below.
  *)
  enrich pk(kA), pk(kAbis), pk(kB).

  induction t.

  (** **Case where t = 0:**  
  This case is trivial thanks to the addition of `pk(kA)`, `pk(kAbis)`
  and `pk(kB)` in the frame.
  *)
  auto.

  rewrite /*.
  by apply IH.

  (** **Case where t = A(i):**  
  The output of this action is the same on both sides. We show that this
  output can be removed from the frame so that we can conclude by
  induction hypothesis.
  We start by expanding all macros and splitting the pairs and function
  applications. We are then left with the two names `n0(i)` and `r0(i)`
  used for the encryption. These names are fresh (_i.e._ does not appear
  anywhere else in the frame) so we are able to remove them with the
  `fresh` tactic.
  *)
  expandall.
  fa 3; fa 4; fa 4; fa 4; fa 4.
  fresh 5; 1:auto.
  by fresh 4.

  (** **Case where t = Abis(ibis):**  
  Similar to the previous case.
  *)
  expandall.
  fa 3; fa 4; fa 4; fa 4; fa 4.
  fresh 5; 1:auto.
  by fresh 4.

  (** **Case where t = B(j):**  
  We have to show that the output message does not give any information
  to the attacker to distinguish the left side from the right side.
  *)

  
  expand frame, output, exec, cond, dmess.
  fa 3; fa 4; fa 4.


  (** We first use the ciphertext indistinguishability (IND-CCA1)
  assumption, which requires to show that the lengths of the plaintexts
  on both sides are equal.
  *)
  cca1 4; [1:auto].

  (** We use the lemma `if_same_len` to push the conditional under len(_),
  and simplify the resulting expression. *)
  rewrite if_same_len in 4.
  (* We use our axiom on the length of a pair. *)
  by rewrite !length_pair.

  rewrite length_pair namelength_n in 4. 

  (**
  Thanks to the IND-CCA assumption, the ciphertext now only encrypts
  publicly known values that do not depend on the side.
  We now use the key privacy assumption: knowing only a ciphertext, it
  should not be possible to know which specific key was used.
  We apply a transitivity step first: enckp is applied on the left system,
  so that the only remaining diff is in 4.
  *)

  trans [default/left,default/left].
  - auto.
  - by crypto Enckp (k0 : kA) (k1 : kAbis).
  - fa enc _. by fresh 4. 
Qed.

