include Basic.

abstract one : message.
abstract ok : message.

mutable cpt : message = zero.

channel c.

(* ================================================================= *)
process reader =
  let x1 = cpt in
  cpt := one;
  let x2 = cpt in
  R:  out(c,<x1,x2>);

  in(c,y);
  R1: out(c, <x1,x2>).

system P = reader.

(* ----------------------------------------------------------------- *)
lemma [P] _ :
  happens(R) => output@R = <cpt@pred R, cpt@R>.
Proof.
  intro Hap. 
  rewrite /output. 
  rewrite /x1 /x2.
  auto.
Qed.

(* ----------------------------------------------------------------- *)
lemma [P] _ :
  happens(R1) => output@R1 = <cpt@pred R, cpt@R>. (* and not `<cpt@pred R1,_>`! *)
Proof.
  intro Hap. 
  rewrite /output. 
  rewrite /x1 /x2.
  auto.
Qed.
