module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Patterns} *)

(** A pattern is a list of free type variables, a term [t] and a subset
    of [t]'s free variables that must be matched.
    The free type variables must be inferred. *)
type 'a pat = {
  pat_tyvars : Type.tvars;
  pat_vars : Sv.t;
  pat_term : 'a;
}

(** Make a pattern out of a formula: all universally quantified variables
    are added to [pat_vars]. *)
val pat_of_form : Term.message -> Term.message pat

(*------------------------------------------------------------------*)
(** {2 Matching variable assignment} *)

module Mvar : sig
  (** Unification and matching variable assignment. *)
  type t

  val empty : t

  (** Union of two [mv] with dijoint supports. *)
  val union : t -> t -> t

  (** remove a variable assignment *)
  val remove : Vars.evar -> t -> t

  (** add a variable assignment *)
  val add : Vars.evar -> Term.eterm -> t -> t

  (** check if a variable is assigned *)
  val mem : Vars.evar -> t -> bool

  val filter : (Vars.evar -> Term.eterm -> bool) -> t -> t

  val fold : (Vars.evar -> Term.eterm -> 'b -> 'b) -> t -> 'b -> 'b

  val to_subst : mode:[`Match | `Unif] -> t -> Term.subst
end

(*------------------------------------------------------------------*)
(** {2 Module signature of matching} *)

type match_res = 
  | FreeTyv
  | NoMatch of (Term.messages * Term.match_infos) option 
  | Match   of Mvar.t

type f_map =
  Term.eterm -> Vars.evars -> Term.message list ->
  [`Map of Term.eterm | `Continue] 

(** matching algorithm options *)
type match_option = {
  mode      : [`Eq | `EntailLR | `EntailRL];
  use_fadup : bool;
}

val default_match_option : match_option

(** Module signature of matching.
    We can only match a [Term.term] into a [Term.term] or a [Equiv.form].
    Hence, the type of term we match into is abstract.
    The type we match from is fixed to Term.term. *)
module type S = sig
  (** Abstract type of terms we are matching in. *)
  type t

  val pp_pat :
    (Format.formatter -> 'a -> unit) ->
    Format.formatter -> 'a pat -> unit

  val unify :
    ?mv:Mvar.t ->
    Symbols.table ->
    t pat -> t pat ->
    [`FreeTyv | `NoMgu | `Mgu of Mvar.t]

  val unify_opt :
    ?mv:Mvar.t ->
    Symbols.table ->
    t pat -> t pat ->
    Mvar.t option

  (** [try_match t p] tries to match [p] with [t] (at head position).
      If it succeeds, it returns a map [θ] instantiating the variables
      [p.pat_vars] as substerms of [t], and:

      - if [mode = `Eq] then [t = pθ] (default mode);
      - if [mode = `EntailLR] then [t = pθ] or [t ⇒ pθ] (boolean case).
      - if [mode = `EntailRL] then [t = pθ] or [pθ ⇒ t] (boolean case). *)
  val try_match :
    ?mv:Mvar.t ->
    ?option:match_option ->
    Symbols.table ->
    SystemExpr.t ->
    t -> t pat ->
    match_res

  (** Same as [try_match], but specialized for terms. *)
  val try_match_term :
    ?mv:Mvar.t ->
    ?option:match_option ->
    Symbols.table ->
    SystemExpr.t ->
    'a Term.term -> 'b Term.term pat ->
    match_res


  (** [map ?m_rec func env t] applies [func] at all position in [t]. 
      If [m_rec] is true, recurse after applying [func].
      [m_rec] default to [false].*)
  val map : ?m_rec:bool -> f_map -> Vars.env -> t -> t option
end

(*------------------------------------------------------------------*)
(** {2 Matching and unification} *)
module T : S with type t = Term.message

module E : S with type t = Equiv.form

