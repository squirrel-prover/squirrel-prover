(*******************************************************************************
# Key-Exchange Protocol

 We consider a toy protocol where a public key is used to exchange a
 symmetric key that is then used to exchange a message -- in real life
 this symmetric key would be used for several messages in a session.

 We have two roles A and B.
 A pair of public/private encryption keys are generated for B,
 called pkB and skB.
 A pair of public/private signature keys are generated for A,
 called spkA and sskA.

 The protocol is as follows:

 - A sends to B sk encrypted with pkB,
   together with a signature of that message using sskA.

 - B sends to A some message x encrypted with sk.

 To model the fact that x is arbitrary, and can even be chosen
 by the attacker, our model for B actually inputs x from the
 network after having received sk.

 Our goal is to show secrecy properties for sk and x.
 To achieve this, we will first show that our protocol is equivalent
 to an idealized version of the protocol where sk is "magically"
 exchanged (actually, pre-shared) hence does not appear on the
 network. As we shall see, this equivalence can be used to greatly
 facilitate proofs about the real protocol. 
*******************************************************************************)

(* ------------------------------------------------------------------- *)

(* Assume some CCA1 asymmetric and symmetric encryptions (which must
   hence be randomized) as well as some EUF signature. *)
aenc asym_enc, asym_dec, enc_pk.

senc sym_enc, sym_dec.

signature sign, checksign, sign_pk.

(* Secret signing key for A. *)
name sskA : message.

(* Secret encryption key for B. *)
name skB : message.

(* The symmetric key that is exchanged in the real protocol. *)
name sk : message.

(* We introduce a constant for representing the security parameter, in unary. *)
abstract eta : message.

(* We assume that this constant has the same length than all names, 
   in particular sk.  *)
axiom [any] len_sk : len(sk) = len(eta).
hint rewrite len_sk.

(* ------------------------------------------------------------------- *)

(* Model two protocols as a bi-process, with the real protocol on the left
   and the idealized one on the right. *)

channel c.

process A(pkB:message) =
  new r;
  (* Send key on the left, or zeroes on the right. *)
  let m = asym_enc(diff(sk,zeroes(eta)),r,pkB) in
  out(c,<m,sign(m,sskA)>).

process B(spkA:message) =
  (* Get the symmetric key. *)
  Brecv:
  in(c,x);
  if checksign(fst(x),snd(x),spkA) then
    (* Send message using received key on the left,
       or magically known key on the right. *)
    in(c,y);
    new rr;
    Bout:
    out(c,sym_enc(y,rr,diff(asym_dec(fst(x),skB),sk)))
  else Bfail: null.

system (let pkB = enc_pk(skB) in
        let spkA = sign_pk(sskA) in
        Pub: out(c,<pkB,spkA>);
        (A(pkB) | B(spkA))).

(* ------------------------------------------------------------------- *)

(* Load basic library of axioms, and add some complement. *)

include Basic.

(* This axiom holds for any bi-system.
   It cannot be stated for [any] hence it is not in the standard library. *)
axiom [default] diff_refl (x:message) : diff(x,x) = x.

(* ------------------------------------------------------------------- *)

(* Useful lemmas for the next proof. *)
print goal exec_le.
print goal exec_cond.

(* In the real protocol, the key obtained after checking the signature
   is sk as expected. *)
goal [default/left] correct_key :
  happens(Bout) => exec@Bout =>
  asym_dec(fst(input@Brecv),skB) = sk.
Proof.
  (* You can use `euf` with a signature on a hypothesis of the
     form `checksign(v,u,sign_pk(k))`. *)
  admit. (* TODO *)
Qed.

(* ------------------------------------------------------------------- *)

(* Show that the real and ideal protocols are observationally equivalent.
   You will actually have to show something strong, by adding more items
   in the equivalence: intuitively, add everything that the attacker can
   learn (after the attack) that still does not help him to distinguish
   the left and right frames.
   Adding more things can make the proof simpler, and also results in
   a stronger lemma that will be useful in the rest of the file. *)
global goal [default] idealize_key_exchange (t:timestamp[const]) :
  [happens(t)] ->
  equiv((* TODO: add something here... *)frame@t).
Proof.
  admit. (* TODO *)
Qed.

(* ------------------------------------------------------------------- *)
(** ## Rewrite equiv *)

(* Before proving interesting things about our protocol, we need to
   introduce an advanced tactic: rewrite equiv. *)

(* Remember that [phi] is the same as [phi ~ true].
   If we have [phi ~ psi] then we can prove [phi] from [psi],
   by transitivity.
   The `rewrite_equiv` tactic does just this, and it guesses
   from [phi] and an equivalence [u1..uN ~ v1..vN] the formula
   [psi] such that [phi ~ psi]: intuitively, it finds a way to
   compute [phi] from [u1..uN] and computes psi in the same way 
   from [v1..vN]. *)

abstract f : message -> message.
abstract g : message -> message.

name n1 : message.
name n2 : message.

(* In this goal we use the same system on the left and right
   so that, intuitively, systems do not matter anymore. *)
global goal [default/left,default/left] rewrite_equiv_0 (x,y,z:message) :
  equiv(x,diff(y,z)) -> [g(z) = f(x)] -> [f(x) = g(y)].
Proof.
  intro H1 H2.
  rewrite equiv H1.
  auto.
Qed.

(* As with `rewrite` we can use `rewrite equiv -H`. *)
global goal [default/left,default/left] rewrite_equiv_1 (x,y,z:message) :
  equiv(x,diff(y,z)) -> [g(y) = f(x)] -> [f(x) = g(z)].
Proof.
  intro H1 H2.
  rewrite equiv -H1.
  auto.
Qed.

(* Show that the following equivalence is false, using `rewrite equiv`.
   You'll have to introduce an intermediate step using `have`.
   Warning: incorrectly using `rewrite equiv` does not cause a failure
   but can result in an unprovable goal. *)
global goal [default/left,default/left] rewrite_equiv_2 :
  equiv(n1,diff(n1,n2)) -> [False].
Proof.
  admit. (* TODO *)
Qed.

(* ------------------------------------------------------------------- *)
(** ## A few more exercices around `rewrite equiv` *)

abstract a : message.
abstract b : message.

hash h.

name k : message.


(* We recall the `hash_5_lemma` we proved in `1-crypto-hash` *)
global goal hash_5_lemma : equiv(diff(h(a,k),n1),n2).
Proof.
  prf 0.
  rewrite if_true // in 0.
  by fresh 0.
Qed.

(* In `1-crypto-hash`, we proved that the following goal using `euf`.
   But actually, this also follows from `prf`. 
   Try proving it without euf but using `hash_5_lemma` instead! *)
goal [default/left] hash_7 : h(a,k) <> n2.
Proof.
  admit. (* TODO *)
Qed.

(* Similarly, prove the next goal without euf or collision. *)
global goal [set:default/left; equiv:default] hash_6 : 
  [a <> b] -> [h(a,k) <> h(b,k)].
Proof.
  admit. (* TODO *)
Qed.

(* ----------------------------------------------------------------- *)
(** ## Back to our protocol *)

(* Weak secrecy of sk.
   We only prove it when Bout is not executed: the property also
   holds afterwards, but the proof would be more difficult.
   Proving this would be trivial for default/right... use rewrite
   equiv to show that this change is justified! *)
goal [default/left] _ (tau:timestamp[glob,const]) :
  happens(pred(tau)) =>
  not(Bout < tau) =>
  not(input@tau = sk).
Proof.
  admit. (* TODO *)
Qed.

(* Using `default` (i.e. `default/left,default/right`) for the `set` part
   of the annotation does not change the meaning of the formula but should
   ease the proof. These annoying details are due to excessive rigidity
   in the current version of the tool. *)
global goal [set: default; equiv: default/left,default/left] _ :
  [happens(Bout)] ->
  equiv(frame@pred(Bout),sym_enc(diff(input@Bout,zeroes(input@Bout)),rr,sk)).
Proof.
  (* As before it would be easier to prove this on default/right...
     This time rewrite requiv is not relevant, but we can just use
     plain transitivity. *)
  help trans.
  admit. (* TODO *)
Qed.
