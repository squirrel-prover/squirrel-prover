(** Extending sequents with functionalities based on proved goals. *)

(** Generalized hypothesis: hypothesis or lemma identifier. *)
type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

(** Sequents with functionalities based on proved goals. *)
module type S = sig
  include LowSequent.S

  (** An assumption can be an hypothesis, an axiom, or a proved goal. *)
  val is_assumption       : Theory.lsymb -> t -> bool
  val is_equiv_assumption : Theory.lsymb -> t -> bool
  val is_reach_assumption : Theory.lsymb -> t -> bool

  (** Get statement associated to an assumption. *)
  val get_assumption :
    'a Equiv.f_kind -> Theory.lsymb -> t -> (ghyp, 'a) Goal.abstract_statement

  val reduce : Reduction.red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val convert_pt_hol :
    Theory.p_pt_hol -> 'a Equiv.f_kind -> t -> ghyp * 'a Match.pat
end

(** Functor building a {!Sequent.S} from a {!LowSequent.S}. *)
module Mk (LS : LowSequent.S) : S with
  type         t = LS.t         and
  type  hyp_form = LS.hyp_form  and
  type conc_form = LS.conc_form
