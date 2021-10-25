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

  val to_general_sequent : t -> Goal.t
                                    
  (** Get statement associated to an assumption.
    * By default it checks for compatibility: this means system inclusion
    * for local assumptions, and system equality otherwise. *)
  val get_assumption :
    ?check_compatibility:bool ->
    'a Equiv.f_kind -> Theory.lsymb -> t -> (ghyp, 'a) Goal.abstract_statement

  val reduce : Reduction.red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  (** Convert a proof term into a pattern and the system it applies to. *)
  val convert_pt_hol_gen :
    ?check_compatibility:bool -> 
    Theory.p_pt_hol -> 
    'a Equiv.f_kind -> t -> 
    ghyp * SystemExpr.t * 'a Match.pat

  (** Same as [convert_pt_hol_gen], when the system is the current system of 
      the sequent. *)
  val convert_pt_hol :
    Theory.p_pt_hol ->
    'a Equiv.f_kind -> t -> 
    ghyp * 'a Match.pat

end

(*------------------------------------------------------------------*)
module type MkArgs = sig
  module S : LowSequent.S
  val to_general_sequent : S.t -> Goal.t
end

(** Functor building a {!Sequent.S} from a {!LowSequent.S}. *)
module Mk (Args : MkArgs) : S with
  type t         = Args.S.t         and
  type conc_form = Args.S.conc_form and
  type hyp_form  = Args.S.hyp_form
