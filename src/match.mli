open Utils

module Sv = Vars.Sv

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {2 Positions} *)

module Pos : sig

  (** A position in a term *)
  type pos

  val pp : Format.formatter -> pos -> unit

  (** set of positions *)
  module Sp : Set.S with type elt = pos

  (*------------------------------------------------------------------*)
  (** strict prefix comparison over positions *)
  val lt : pos -> pos -> bool
    
  (*------------------------------------------------------------------*)
  (** [f] of type [f_sel] is a function that, given [t projs vars conds] where:
      - [t] is sub-term of the term we are mapping one
      - [projs] are the projections applying to [t], if any
      - [vars] are the free variable bound above [t]'s occurrence
      - [conds] are conditions above [t]'s occurrence

      If [f t vars conds = `Select], we found a position.
      If [f t vars conds = `Continue], we keep looking for positions downwards. *)
  type f_sel =
    Term.term -> Term.projs option -> Vars.vars -> Term.term list ->
    [`Select | `Continue]

  (*------------------------------------------------------------------*)
  (** [select f t] compute the positions in [t] selected by [f]. *)
  val select : f_sel -> Term.term -> Sp.t

  (** Same as [select], except that is acts on [Equiv.form]. Note that we 
      can only select [Term.term] positions. *)
  val select_e : f_sel -> Equiv.form -> Sp.t

  (*------------------------------------------------------------------*)
  (** [f] of type ['a f_map_fold] is a function that, given 
      [t se vars conds p acc] where:
      - [t] is sub-term of the term we are mapping one
      - [se] is the system expr applying to [t]
      - [vars] are the free variable bound above [t]'s occurrence
      - [conds] are conditions above [t]'s occurrence
      - [p] is the position of [t]'s occurrence

      If [f t projs vars conds p acc =]:
      - [`Select], we found a position.
      - [`Continue], we keep looking for positions downwards. *)
  type 'a f_map_fold =
    Term.term ->
    SE.arbitrary -> Vars.vars -> Term.term list -> pos ->
    'a ->
    'a * [`Map of Term.term | `Continue]

  (** Same as [f_map_fold], but just for a map. *)
  type f_map =
    Term.term ->
    SE.arbitrary -> Vars.vars -> Term.term list -> pos -> 
    [`Map of Term.term | `Continue]

  (*------------------------------------------------------------------*)
  (** [map_fold ?mode func env acc t] applies [func] at all position in [t].

      Tree traversal can be controlled using [mode]:
      - [`TopDown b]: apply [func] at top-level first, then recurse.
        [b] tells if we recurse under successful maps.
      - [`BottomUp _]: recurse, then apply [func] at top-level *)
  val map_fold : 
    ?mode:[`TopDown of bool | `BottomUp] -> 
    'a f_map_fold ->            (* folding function *)
    Vars.env ->                 (* for clean variable naming *)
    SE.arbitrary ->
    'a ->                       (* folding value *)
    Term.term -> 
    'a * bool * Term.term       (* folding value, `Map found, term *)

  (** Same as [map_fold] for [Equiv.form]. *)
  val map_fold_e : 
    ?mode:[`TopDown of bool | `BottomUp] -> 
    'a f_map_fold ->            (* folding function *)
    Vars.env ->                 (* for clean variable naming *)
    SE.context ->
    'a ->                       (* folding value *)
    Equiv.form -> 
    'a * bool * Equiv.form      (* folding value, `Map found, term *)

  (*------------------------------------------------------------------*)
  (** Same as [map_fold], but only a map. 
      Return: `Map found, term *)
  val map : 
    ?mode:[`TopDown of bool | `BottomUp] ->
    f_map ->
    Vars.env ->
    SE.arbitrary ->
    Term.term ->
    bool * Term.term

  (** Same as [map_fold_e], but only a map.
      Return: `Map found, term *)
  val map_e :
    ?mode:[`TopDown of bool | `BottomUp] ->
    f_map ->
    Vars.env ->
    SE.context ->
    Equiv.form ->
    bool * Equiv.form
end

(*------------------------------------------------------------------*)
(** {2 Term heads} *)

type term_head =
  | HExists
  | HForAll
  | HSeq
  | HFind
  | HFun   of Symbols.fname 
  | HMacro of Symbols.macro 
  | HName  of Symbols.name  
  | HDiff
  | HVar
  | HAction

val pp_term_head : Format.formatter -> term_head -> unit

val get_head : Term.term -> term_head

module Hm : Map.S with type key = term_head

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

val project_tpat     : Term.projs        -> Term.term pat -> Term.term pat
val project_tpat_opt : Term.projs option -> Term.term pat -> Term.term pat

(** Make a pattern out of a formula: all universally quantified variables
    are added to [pat_vars]. *)
val pat_of_form : Term.term -> Term.term pat

(*------------------------------------------------------------------*)
(** {2 Matching variable assignment} *)

module Mvar : sig
  (** Unification and matching variable assignment. *)
  type t

  val empty : t

  (** Union of two [mv] with dijoint supports. *)
  val union : t -> t -> t

  (** remove a variable assignment *)
  val remove : Vars.var -> t -> t

  (** add a variable assignment *)
  val add : Vars.var -> Term.term -> t -> t

  (** check if a variable is assigned *)
  val mem : Vars.var -> t -> bool

  val filter : (Vars.var -> Term.term -> bool) -> t -> t

  val fold : (Vars.var -> Term.term -> 'b -> 'b) -> t -> 'b -> 'b

  val to_subst : mode:[`Match | `Unif] -> t -> Term.subst

  val pp : Format.formatter -> t -> unit
end

(*------------------------------------------------------------------*)
(** {2 Module signature of matching} *)

type match_res =
  | FreeTyv
  | NoMatch of (Term.terms * Term.match_infos) option
  | Match   of Mvar.t

(** matching algorithm options *)
type match_option = {
  mode          : [`Eq | `EntailLR | `EntailRL];
  use_fadup     : bool;
  allow_capture : bool;
  (** allow pattern variables to capture bound variables (i.e. to be
      instantiated by terms using bound variables). 
      When doing rewriting, lemma application, etc, must be false. *)
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

  (** [try_match ... t p] tries to match [p] with [t] (at head position).
      If it succeeds, it returns a map [θ] instantiating the variables
      [p.pat_vars] as subterms of [t], and:

      - if [mode = `Eq] then [t = pθ] (default mode);
      - if [mode = `EntailLR] then [t = pθ] or [t ⇒ pθ] (boolean case).
      - if [mode = `EntailRL] then [t = pθ] or [pθ ⇒ t] (boolean case). *)
  val try_match :
    ?option:match_option ->
    ?mv:Mvar.t ->
    ?ty_env:Type.Infer.env ->
    Symbols.table ->
    SE.context -> 
    t -> 
    t pat ->
    match_res

  (** [find pat t] returns the list of occurences in t that match the
     pattern. *)
  val find : 
    ?option:match_option ->
    Symbols.table ->
    SE.context ->
    Vars.env ->
    Term.term pat -> 
    t -> 
    Term.term list
end

(*------------------------------------------------------------------*)
(** {2 Matching and unification} *)
module T : S with type t = Term.term

module E : S with type t = Equiv.form
