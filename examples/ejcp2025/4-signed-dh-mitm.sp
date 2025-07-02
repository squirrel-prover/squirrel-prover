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
  (A: in(c, pkC); A(skA,pkC) | (* Alice 🙂 is willing to talk to anyone, even Charlie 😈*)
   B: B(skB,pkA)).



(* g^x^y is still secret *)
lemma secret (t:timestamp) : 
  happens(t) => 
  g^(x ** y) <> att(frame@t).
Proof.
  (* TODO *)
Abort.


(* The key derived by Bob is still secret *)
(* (not the key derived by Alice of course) *)
lemma better_secret (t:timestamp) :
  happens(t,B1) => 
  exec@B1 => 
  X'@B1^y <> att(frame@t).
Proof.
  (* TODO *)
Abort.

(* However Bob does not authenticate A correctly. *)

lemma auth_B : 
  happens(B1) => 
  exec@B1 => 
  A1 < B1 && input@A = pkB@PUB && X'@B = X@A1 && Y@B = Y'@A1.
Proof.
  (* TODO try to see where the proof fails *)
Abort.


(* TODO modify the protocol as in the lecture and
   prove that it fixes the authentication issue. *)
