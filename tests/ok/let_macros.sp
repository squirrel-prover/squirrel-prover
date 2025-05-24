include Core.

abstract one   : message.
abstract two   : message.
abstract three : message.
abstract ok : message.

mutable cpt : message = zero.

channel c.

(* ================================================================= *)
process Qreader =
  let x = one in
  R:  out(c,x);

  in(c,y);
  R1: out(c, x).

system Q = Qreader.

(* ----------------------------------------------------------------- *)
lemma [Q] _ :
  happens(R) => output@R = one.
Proof.
  intro Hap.
  rewrite /output.
  rewrite /x.
  auto.
Qed.

(* ----------------------------------------------------------------- *)
lemma [Q] _ :
  happens(R1) => output@R1 = one.
Proof.
  intro Hap.
  rewrite /output.
  rewrite /x.
  auto.
Qed.


(* ================================================================= *)
process Lreader =
  let z = one in
  ((R: out(c, <z,zero>); !_i R2: out(c, <z,one  >)) |
   (A: out(c, <z,two >); !_i A2: out(c, <z,three>)  )).

system L = Lreader.

(* ----------------------------------------------------------------- *)
lemma [L] _ :
  happens(R1) => output@R1 = <one,zero>.
Proof.
  intro Hap. 
  rewrite /output. 
  rewrite /z.
  auto.
Qed.

lemma [L] _ i :
  happens(R2 i) => output@R2 i = <one,one>.
Proof.
  intro Hap. 
  rewrite /output.
  rewrite /z.
  auto.
Qed.

(* ----------------------------------------------------------------- *)
lemma [L] _ :
  happens(A) => output@A = <one,two>.
Proof.
  intro Hap. 
  rewrite /output. 
  rewrite /z.
  auto.
Qed.

lemma [L] _ i :
  happens(A2 i) => output@A2 i = <one,three>.
Proof.
  intro Hap. 
  rewrite /output. 
  rewrite /z.
  auto.
Qed.
