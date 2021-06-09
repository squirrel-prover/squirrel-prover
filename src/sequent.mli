(** Sequents with functionalities based on proved goals. *)
module type S = sig
  include LowSequent.S

  val is_hyp_or_lemma        : Theory.lsymb -> t -> bool
  val is_equiv_hyp_or_lemma  : Theory.lsymb -> t -> bool
  val is_reach_hyp_or_lemma  : Theory.lsymb -> t -> bool

  val get_k_hyp_or_lemma :
    'a Equiv.f_kind -> Theory.lsymb -> t -> (Goal.ghyp, 'a) Goal.lemma_g

  val reduce : Reduction.red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val convert_pt_hol :
    Theory.p_pt_hol -> 'a Equiv.f_kind -> t -> Goal.ghyp * 'a Match.pat
end

(** Functor building a {!Sequent.S} from a {!LowSequent.S}. *)
module Mk (LS : LowSequent.S) : S with
  type         t = LS.t         and
  type  hyp_form = LS.hyp_form  and
  type conc_form = LS.conc_form
