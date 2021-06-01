(** Sequents with functionalities based on proved goals. *)
module type S = sig
  include LowSequent.S

  val is_hyp_or_lemma        : Theory.lsymb -> t -> bool
  val is_equiv_hyp_or_lemma  : Theory.lsymb -> t -> bool
  val is_reach_hyp_or_lemma  : Theory.lsymb -> t -> bool

  val get_hyp_or_lemma       : Theory.lsymb -> t -> Goal.hyp_or_lemma
  val get_equiv_hyp_or_lemma : Theory.lsymb -> t -> Goal.equiv_hyp_or_lemma
  val get_reach_hyp_or_lemma : Theory.lsymb -> t -> Goal.reach_hyp_or_lemma
  val get_k_hyp_or_lemma :
    'a LowSequent.s_kind -> Theory.lsymb -> t -> (Goal.ghyp, 'a) Goal.lemma_g

  val reduce : Reduction.red_param -> t -> form -> form

  val convert_pt_hol :
    Theory.p_pt_hol -> 'a LowSequent.s_kind -> t -> Goal.ghyp * 'a Term.pat
end

(** Functor building a {!Sequent.S} from a {!LowSequent.S}. *)
module Mk (LS : LowSequent.S) : S with type t = LS.t and type form = LS.form
