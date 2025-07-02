(*******************************************************************

# Tutorial: the Diffie-Hellman key exchange

 *******************************************************************)

(* Setup (loads standard squirrel libraries) *)
include Logic.


(* --------------------------------------------------------------------- *)
(** ## Declaring a Diffie-Hellman group *)
type exponent.
cdh g, (^), ( ** ) where group:message exponents:exponent.


(* --------------------------------------------------------------------- *)
(** ## Declaring a signature scheme.
    Implicitly assumes EUF-CMA, which is made available through the euf tactic.
    Also assumes that verify(m, sign(m, sk), pk(sk)) = true.  *)
type skey.
signature sign, verify, pk where pk:message sk:skey.


channel c.


abstract 👍 : message.
abstract 👎 : message.

(* Alice 🙂 *)
process A (skA:skey,pkB:message) =
  new x:exponent;
  let X = g^x in
  out(c,X);
  in(c,m);
  let Y' = fst m in
  let s = snd m in
  if verify(<Y',X>,s,pkB) then
    out(c,sign(<X,Y'>,skA))
  else
    out(c,👎).

(* Bob 😊 *)
process B (skB:skey,pkA:message) =
  new y:exponent;
  let Y = g^y in
  in(c,x');
  let X' = x' in
  out(c,<Y,sign(<Y,X'>,skB)>);
  in(c,s);
  if verify(<X',Y>,s,pkA) then
    out(c,👍)
  else
    out(c,👎).

system default =
  new skA:skey;
  new skB:skey;
  let pkA = pk skA in
  let pkB = pk skB in
  PUB: out(c,<pkA,pkB>);
  (A: A(skA,pkB) |
   B: B(skB,pkA)).


(* --------------------------------------------------------------------- *)
(** ## Secrecy of the exchanged secret *)


(** First, naïve version: g ^ x ^ y remains secret all along the trace. *)
lemma secret (t:timestamp) :
  happens(t) =>
  g^(x ** y) <> att(frame@t).
Proof.
  (* TODO *)
Abort.


(** Better formulation: the key derived by Alice is secret. *)
lemma better_secret (t:timestamp) :
  happens(t,A1) =>
  exec@A1 =>
  Y'@A1^x <> att(frame@t).
Proof.
  (* TODO *)
Abort.



(* --------------------------------------------------------------------- *)
(** ## Key agreement *)

(** B authenticates A: when B correctly finishes the protocol,
    A must have as well and A, B must agree on the values of g^x, g^y *)
lemma auth_B :
  happens(B1) => 
  exec@B1 =>
  A1 < B1 && X'@B1 = X@A1 && Y@B1 = Y'@A1.
Proof.
  (* TODO *)
Abort.
