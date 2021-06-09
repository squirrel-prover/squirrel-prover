module Sv = Vars.Sv

(*------------------------------------------------------------------*)
(** {2 Matching and rewriting} *)

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
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.system_expr ->
    t -> t pat ->
    [ `FreeTyv | `NoMatch | `Match of Mvar.t ]

  (** Same as [try_match], but specialized for terms. *)
  val try_match_term :
    ?mv:Mvar.t ->
    ?mode:[`Eq | `EntailLR | `EntailRL] ->
    Symbols.table ->
    SystemExpr.system_expr ->
    'a Term.term -> 'b Term.term pat ->
    [ `FreeTyv | `NoMatch | `Match of Mvar.t ]

  (** [find_map env t p func] looks for an occurence [t'] of [pat] in [t],
      where [t'] is a subterm of [t] and [t] and [t'] are unifiable by [θ].
      It then computes the term obtained from [t] by replacing:
      - if [many = false], a *single* occurence of [pat] by [func t' θ].
      - if [many = true], all occurences found. *)
  val find_map :
    many:bool ->
    Symbols.table ->
    SystemExpr.system_expr ->
    Vars.env ->
    t -> 'a Term.term pat ->
    ('a Term.term -> Vars.evars -> Mvar.t -> 'a Term.term) ->
    t option
end

module T : S with type t = Term.message

module E : S with type t = Equiv.form
