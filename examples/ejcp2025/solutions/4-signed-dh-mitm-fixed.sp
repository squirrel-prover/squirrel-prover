(*******************************************************************

# Tutorial: the Diffie-Hellman key exchange
# MITM and fix

 *******************************************************************)

(* Setup (loads standard squirrel libraries) *)
include Logic.



(* --------------------------------------------------------------------- *)
(** ## Declaring a Diffie-Hellman group and signature scheme*)

type exponent.
cdh g, (^), ( ** ) where group:message exponents:exponent.

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
  if verify(<pk skA, <Y',X>>,s,pkB) then
    out(c,sign(<pkB,<X,Y'>>,skA))
  else
    out(c,👎).


(* Bob 😊 *)
process B (skB:skey,pkA:message) =
  new y:exponent;
  let Y = g^y in
  in(c,x');
  let X' = x' in
  out(c,<Y,sign(<pkA,<Y,X'>>,skB)>);
  in(c,s);
  if verify(<pk skB, <X',Y>>,s,pkA) then
    out(c,👍)
  else
    out(c,👎).

system default =
  new skA:skey; 
  new skB:skey;
  let pkA = pk skA in
  let pkB = pk skB in
  PUB: out(c,<pkA,pkB>);
  (A: in(c, pkC); A(skA,pkC) | (* Alice 🙂 is willing to talk to anyone, even Charlie 😈*)
   B: B(skB,pkA)).



(* g^x^y is still secret *)
lemma secret (t:timestamp) : 
  happens(t) => 
  g^(x ** y) <> att(frame@t).

Proof.
  intro Hap Heq.
  cdh Heq, g.
Qed.

(* The key derived by Bob is still secret *)
(* (not the key derived by Alice of course) *)
lemma better_secret (t:timestamp) :
  happens(t,B1) => 
  exec@B1 => 
  X'@B1^y <> att(frame@t).
Proof.
  rewrite /exec /cond.
  intro Hap [He Hv] Heq.
  euf Hv.
  intro [Hl Hp].
  have Hx : X'@B = X@A by auto.
  rewrite Hx /X in Heq. 
  cdh Heq, g. 
Qed.


(* Bob now authenticates Alice correctly. *)
lemma auth_B : 
  happens(B1) => 
  exec@B1 => 
  A1 < B1 && input@A = pkB@PUB && X'@B = X@A1 && Y@B = Y'@A1.
Proof.
  rewrite /exec /cond.
  intro Hap [He Hc].
  euf Hc.
  intro [Hl Hp].
  repeat split.
  + (* For the first subgoal auto cannot conclude
       because it does not know that A < A1. *)
    have _ : B < B1.
    search B < B1. (* search can be used to find the relevant lemma *)
    apply depends_B_B1.
    auto.
    auto.
  + auto.
  + auto.
  + auto.
Qed.
