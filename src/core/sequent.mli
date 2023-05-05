(** Extending sequents with functionalities based on proved goals. *)

module Sv = Vars.Sv
module Mvar = Match.Mvar
module SE = SystemExpr

(*------------------------------------------------------------------*) 
module PT : sig
  (** A proof-term conclusion.
      For now, we do not keep the proof-term itself. *)
  type t = {
    system : SE.context;
    args   : (Vars.var * Vars.Tag.t) list;
    (** in reversed order w.r.t. introduction *)

    mv     : Mvar.t;
    subgs  : Equiv.any_form list;
    form   : Equiv.any_form;
  }

  val pp : Format.formatter -> t -> unit
end

(*------------------------------------------------------------------*) 
(** Try to cast [pt_f] as a [kind] proof-term conclusion. 
    Raise [failed] in case of failure. *)
val pt_try_cast :
  failed:(unit -> PT.t) ->
  'a Equiv.f_kind -> 
  PT.t -> PT.t

(*------------------------------------------------------------------*) 
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
  (** Convert a parsed proof term into a proof-term.
      If [close_pats] is [false], pattern variables that cannot be
      inferred remains (default to [true]).
      Also return the head of the proof term as a [ghyp], and
      subgoals to prove. *)
  val convert_pt_gen :
    check_compatibility:bool ->
    ?close_pats:bool ->
    Theory.p_pt -> 
    t ->
    ghyp * Type.tvars * PT.t

  (** Same as [convert_pt_gen], when the system is the current system of
      the sequent. *)
  val convert_pt :
    ?close_pats:bool ->
    Theory.p_pt -> 
    t ->
    ghyp * Type.tvars * PT.t
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
