include Real. 
open Real.

system null.

(* Global case, advantages do not change. *)

(* In a local judgement. *)
global lemma _ phi psi b : ([phi <: b] \/ [psi <: b]) -> [phi || psi <: b].
Proof.
  intro H.
  case H.
  + left. auto.
  + right. auto.
Qed.

(* In a global judgement. *)
global lemma _ phi psi b : ([phi <: b] \/ [psi <: b]) -> ([phi <: b] \/ [psi <: b]).
Proof.
  intro H.
  case H.
  + left. auto.
  + right. auto.
Qed.

(*------------------------------------------------------------------*)
global axiom toto_ax toto foo b : [toto = 42] -> [foo <: b].
global axiom tutu_ax tutu foo b : [tutu = 24] -> [foo <: b].

(* Global case analysis in a local judgement leaves the advantages
   unchanged, no matter the formulas. 
   Here, we purposedly have asymptotic premises. *)
global lemma _ toto tutu foo b : ([toto = 42] \/ [tutu = 24]) -> [foo <: b].
Proof.
  intro H.
  case H.
  + apply toto_ax _ foo b in H. assumption H.
  + apply tutu_ax _ foo b in H. assumption H.
Qed.
