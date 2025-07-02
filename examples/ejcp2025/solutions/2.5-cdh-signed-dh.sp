include Logic.
system null.

(** ## Declaring a Diffie-Hellman group *)
type exponent.
cdh g, (^), ( ** ) where group:message exponents:exponent.

(** ## Declaring a signature scheme.
    Implicitly assumes EUF-CMA, which is made available through the euf tactic.
    Also assumes that verify(m, sign(m, sk), pk(sk)) = true.  *)
type skey.
signature sign, verify, pk where pk:message sk:skey.

name x : exponent.
name y : exponent.
name sk😊 : skey.

let pk😊 = pk sk😊.

let out1 = g^x.
let in2  = att(<out1,empty>).
let out2 = < g^y, sign(<g^y,in2>,sk😊) >.
let in3  = att(<out2,<out1,empty>>).

lemma _ : in3 <> g^x^y.
Proof.
  intro H.
  cdh H, g.
Qed.

lemma _ :
  verify(<fst(in3),g^x>,snd(in3),pk😊) =>
  fst(in3) = g^y &&
  in2 = g^x.
Proof.
  intro H.
  euf H.
  auto.
Qed.
