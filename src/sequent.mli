type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Module type for sequents -- after Prover} *)

module type S = sig
  include LowSequent.S

  val is_hyp_or_lemma        : lsymb -> t -> bool
  val is_equiv_hyp_or_lemma  : lsymb -> t -> bool
  val is_reach_hyp_or_lemma  : lsymb -> t -> bool

  val get_hyp_or_lemma       : lsymb -> t -> Goal.hyp_or_lemma
  val get_equiv_hyp_or_lemma : lsymb -> t -> Goal.equiv_hyp_or_lemma
  val get_reach_hyp_or_lemma : lsymb -> t -> Goal.reach_hyp_or_lemma

  val reduce : t -> form -> form
end
