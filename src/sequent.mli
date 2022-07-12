(** Extending sequents with functionalities based on proved goals. *)

(** Generalized hypothesis: hypothesis or lemma/axiom identifier. *)
type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

(** Sequents with functionalities based on proved goals. *)
module type S = sig
  include LowSequent.S

  (*------------------------------------------------------------------*) 
  (** reduction functions *)
  module Reduce : Reduction.S with type t := t

  (*------------------------------------------------------------------*) 
  (** An assumption can be an hypothesis, an axiom, or a proved goal. *)
  val is_assumption       : Theory.lsymb -> t -> bool
  val is_equiv_assumption : Theory.lsymb -> t -> bool
  val is_reach_assumption : Theory.lsymb -> t -> bool

  (*------------------------------------------------------------------*) 
  val to_general_sequent : t -> Goal.t

  (** Transform any sequent into a global sequent. Drop local
      hypotheses that no longer apply.
      Conclusion defaults to [Equiv.False]. *)
  val to_global_sequent : t -> LowEquivSequent.t

  (*------------------------------------------------------------------*) 
  (** Convert a proof term into a pattern and the system it applies to.
      The pattern is the conclusion of the proof term.
      If [close_pats] is [false], pattern variables that cannot be
      inferred remains (default to [true]).
      Also return the head of the proof term as a [ghyp], and
      subgoals to prove. *)
  val convert_pt_gen :
    check_compatibility:bool ->
    ?close_pats:bool ->
    Theory.p_pt ->
    'a Equiv.f_kind -> t ->
    ghyp * SystemExpr.context * 'a list * 'a Term.pat

  (** Same as [convert_pt_gen], when the system is the current system of
      the sequent. *)
  val convert_pt :
    ?close_pats:bool ->
    Theory.p_pt ->
    'a Equiv.f_kind -> t ->
    ghyp * 'a list * 'a Term.pat

end

(*------------------------------------------------------------------*)
module type MkArgs = sig
  module S : LowSequent.S

  val to_general_sequent : S.t -> Goal.t
  val to_global_sequent  : S.t -> LowEquivSequent.t
end

(** Functor building a {!Sequent.S} from a {!LowSequent.S}. *)
module Mk (Args : MkArgs) : S with
  type t         = Args.S.t         and
  type conc_form = Args.S.conc_form and
  type hyp_form  = Args.S.hyp_form
