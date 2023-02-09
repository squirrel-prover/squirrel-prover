open Utils

module Sv = Vars.Sv

module SE = SystemExpr

(*------------------------------------------------------------------*)
(** {2 Positions} *)

module Pos : sig

  (** A position in a term *)
  type pos

  val pp : Format.formatter -> pos -> unit

  val root : pos

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
      - [t] is sub-term of the term we are mapping on
      - [se] is the system expr applying to [t]
      - [vars] are the free variable bound above [t]'s occurrence
      - [conds] are conditions above [t]'s occurrence
      - [p] is the position of [t]'s occurrence

      If [f t projs vars conds p acc =]:
      - [`Map t'], we found a position and replace it with [t'].
      - [`Continue], we keep looking for positions downwards or upwards. *)
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

  (** Same as [f_map_fold], but just for a fold. *)
  type 'a f_fold =
    Term.term ->
    SE.arbitrary -> Vars.vars -> Term.term list -> pos ->
    'a ->
    'a

  (*------------------------------------------------------------------*)
  (** [map_fold ?mode func env acc t] applies [func] at all position in [t].

      Tree traversal can be controlled using [mode]:
      - [`TopDown b]: apply [func] at top-level first, then recurse.
        [b] tells if we recurse under successful maps.
      - [`BottomUp _]: recurse, then apply [func] at top-level *)
  val map_fold : 
    ?mode:[`TopDown of bool | `BottomUp] -> 
    'a f_map_fold ->            (* folding function *)
    SE.arbitrary ->
    'a ->                       (* folding value *)
    Term.term -> 
    'a * bool * Term.term       (* folding value, `Map found, term *)

  (** Same as [map_fold] for [Equiv.form]. *)
  val map_fold_e : 
    ?mode:[`TopDown of bool | `BottomUp] -> 
    'a f_map_fold ->            (* folding function *)
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
    SE.arbitrary ->
    Term.term ->
    bool * Term.term

  (** Same as [map_fold_e], but only a map.
      Return: `Map found, term *)
  val map_e :
    ?mode:[`TopDown of bool | `BottomUp] ->
    f_map ->
    SE.context ->
    Equiv.form ->
    bool * Equiv.form

  (*------------------------------------------------------------------*)
  (** Same as [map_fold], but only a fold. *)
  val fold : 
    ?mode:[`TopDown of bool | `BottomUp] -> 
    'a f_fold ->
    SE.arbitrary ->
    'a ->
    Term.term -> 
    'a

  (** Same as [map_fold_e], but only a fold. *)
  val fold_e : 
    ?mode:[`TopDown of bool | `BottomUp] -> 
    'a f_fold ->
    SE.context ->
    'a ->
    Equiv.form -> 
    'a

  (*------------------------------------------------------------------*)
  (** Same as [fold], but only folds on subterms at depth 1.
      Takes as additional input the condition at the current point,
      to propagate it when folding *)
  val fold_shallow : 
    'a f_fold ->          (* function to apply on each subterm at depth 1 *)
    se:SE.arbitrary ->    (* system expr for the current position *)
    fv:Vars.vars ->       (* variables bound above the current position *)
    cond:Term.terms ->    (* conditions for the current position *)
    p:pos ->              (* current position *)
    'a ->                 (* folding value *)
    Term.term ->          (* current term *)
    'a                    (* new folding value *)
end

(*------------------------------------------------------------------*)
(** {2 Matching variable assignment} *)

module Mvar : sig
  type t
  val empty : t

  (** union of two [mv] with disjoint supports *)
  val union : t -> t -> t

  (** remove a variable assignment *)
  val remove : Vars.var -> t -> t

  (** Add a variable assignment. 
      The system indicate how to interpret the assignment. *)
  val add : Vars.tagged_var -> SE.t -> Term.term -> t -> t

  (** check if a variable is assigned *)
  val mem : Vars.var -> t -> bool

  val find : Vars.var -> t -> Term.term

  val is_empty : t -> bool

  val filter : (Vars.var -> (Vars.Tag.t * SE.t * Term.term) -> bool) -> t -> t

  val map : (Term.term -> Term.term) -> t -> t

  val mapi : (Vars.var -> SE.t -> Term.term -> Term.term) -> t -> t

  val fold :
    (Vars.var -> (Vars.Tag.t * SE.t * Term.term) -> 'b -> 'b) -> t -> 'b -> 'b

  (** [table] and [env] are necessary to check that restrictions on 
      variables instanciation have been respected. *)
  val to_subst :
    mode:[`Match|`Unif] ->
    Symbols.table -> Vars.env ->
    t ->
    [`Subst of Term.subst | `BadInst of Format.formatter -> unit]

  (** [to_subst] when all matched (or unified) variables are unrestricted 
      variables (i.e. local variables).
      Indeed, in that case the substitution resolution cannot fail. *)
  val to_subst_locals :
    mode:[`Match|`Unif] -> t -> Term.subst

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
    Format.formatter -> 'a Term.pat -> unit

  (** [try_match ... t p] tries to match [p] with [t] (at head position).
      If it succeeds, it returns a map [θ] instantiating the variables
      [p.pat_vars] as subterms of [t], and:

      - if [mode = `Eq] then [t = pθ] (default mode);
      - if [mode = `EntailLR] then [t = pθ] or [t ⇒ pθ] (boolean case).
      - if [mode = `EntailRL] then [t = pθ] or [pθ ⇒ t] (boolean case). *)
  val try_match :
    ?option:match_option ->
    ?mv:Mvar.t ->
    ?env:Vars.env ->            (* used to get variables tags *)
    ?ty_env:Type.Infer.env ->
    ?hyps:Hyps.TraceHyps.hyps Lazy.t ->
    ?expand_context:Macros.expand_context ->
    Symbols.table ->
    SE.context -> 
    t -> 
    t Term.pat ->
    match_res

  (** [find pat t] returns the list of occurences in t that match the
      pattern. *)
  val find : 
    ?option:match_option ->
    ?ty_env:Type.Infer.env ->
    Symbols.table ->
    SE.context ->
    Term.term Term.pat -> 
    t -> 
    Term.term list

end

(*------------------------------------------------------------------*)
(** {2 Reduction utilities} *)

(** Expand once at head position. 
    Throw [exn] in case of failure. *)
val expand_head_once :
  exn:exn -> 
  mode:Macros.expand_context ->
  Symbols.table -> SE.t -> Hyps.TraceHyps.hyps Lazy.t ->
  Term.term ->
  Term.term * bool 

(** projection reduction *)
val reduce_proj : Term.term -> Term.term * bool 

(** β-reduction *)
val reduce_beta : Term.term -> Term.term * bool 

(*------------------------------------------------------------------*)
(** {2 Matching and unification} *)
module T : S with type t = Term.term

module E : sig
  include S with type t = Equiv.form
  val find_glob : 
    ?option:match_option ->
    ?ty_env:Type.Infer.env ->
    Symbols.table ->
    SE.context ->
    t Term.pat -> 
    t -> 
    t list
end
