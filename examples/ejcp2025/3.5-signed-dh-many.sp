(*******************************************************************

# Tutorial: the Diffie-Hellman key exchange
# Many sessions

 *******************************************************************)

(* Setup (loads standard squirrel libraries) *)
include Logic.

(* --------------------------------------------------------------------- *)
(** ## Declaring a Diffie-Hellman group and signature scheme *)
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
  (!_i A: A(skA,pkB) | (* unbounded number of instances of A, B *)
   !_j B: B(skB,pkA) ).


(** All instances of g ^ x ^ y remain secret. *)
lemma secret (t:timestamp) (i,j:index) :
  happens(t) =>
  g^(x i ** y j) <> att(frame@t).
Proof.
  admit. (* TODO *)
Qed.

(** Any key derived by Alice is secret. *)
lemma better_secret (t:timestamp,i:index) :
  happens(t,A1 i) =>
  exec@(A1 i) =>
  Y' i @ (A1 i) ^ x i <> att(frame@t).
Proof.
  admit. (* TODO *)
Qed.

(** Key agreement. *)
lemma auth_B (j:index) :
  happens(B1 j) =>
  cond@B1 j =>
  exists i, A1 i < B1 j              &&
            X' j @ B j = X i  @ A i  &&
            Y j  @ B j = Y' i @ A1 i.
Proof.
  admit. (* TODO *)
Qed.
