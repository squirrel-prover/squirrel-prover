module L = Location

(** A system expression is used to indicate to which systems a formula
    applies. Some formulas apply to any system, others apply to any number of
    systems, and equivalence formulas only make sense relative to
    a pair of systems. *)

(** Expressions denoting sets of single systems.
    When a local formula is annotated with one such expression
    it means that it holds for all systems in the set.

    An [arbitrary expr] can be any set, it practice we use it only
    to denote the set of all systems.

    A [compatible expr] denotes a set of compatible systems,
    which makes it possible to interpret formulas with actions.

    Formulas with macros can only be interpreted in finite sets,
    represented by an [fset expr]. These sets are actually labelled,
    ordered and non-empty.

    An equivalence must be annotated with a [pair expr], representing
    an ordered and labelled pair. *)
type +'a expr

(** Hierarchy of subtypes used as phantom types. *)
type arbitrary  = < > expr
type compatible = < symbols : unit > expr
type fset       = < symbols : unit ; fset : unit > expr
type pair       = < symbols : unit ; fset : unit ; pair : unit > expr

type t = arbitrary

type equiv_t = pair

(*------------------------------------------------------------------*)
val hash : 'a expr -> int

val pp : Format.formatter -> 'a expr -> unit

(** System expression denoting all possible systems.
    It is typically used for axioms or lemmas about primitives. *)
val any : arbitrary

(** System expression denoting all possible systems
    compatible with a given system. *)
val any_compatible_with : System.t -> compatible

(** [subset s1 s2] iff [s1] is included in [s2]. *)
val subset : Symbols.table -> 'a expr -> 'a expr -> bool

val equal : Symbols.table -> 'a expr -> 'a expr -> bool

val is_fset : t -> bool

val is_any_or_any_comp : t -> bool

(** Check that all systems in two expressions are compatible. *)
val compatible : Symbols.table -> 'a expr -> 'b expr -> bool

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type error =
  | Invalid_projection
  | Missing_projection
  | Incompatible_systems
  | Expected_compatible
  | Expected_fset
  | Expected_pair

exception Error of error

val pp_error : Format.formatter -> error -> unit

(*------------------------------------------------------------------*)
(** {2 Conversions} *)

(** Cast expr to arbitrary. Always succeeds. *)
val to_arbitrary : 'a expr -> arbitrary

(** Cast expression to fset if possible,
    fail with [Error Expected_compatible] otherwise. *)
val to_compatible : 'a expr -> compatible

(** Cast expression to fset if possible,
    fail with [Error Expected_fset] otherwise. *)
val to_fset : 'a expr -> fset

(** Convert expression to fset if possible,
    fail with [Error Expected_pair] otherwise. *)
val to_pair : 'a expr -> pair

(*------------------------------------------------------------------*)
(** {2 Actions symbols} *)

(** Get the table of action descriptions of a system expression. *)
val symbs :
  Symbols.table ->
  <symbols:unit;..> expr ->
  Symbols.action System.Msh.t

(** Convert action to the corresponding timestamp term. *)
val action_to_term :
  Symbols.table -> <symbols:unit;..> expr -> Action.action -> Term.term

(** List of action, symbol and list of indices,
    for each action of compatible systems. *)
val actions :
  Symbols.table ->
  <symbols:unit;..> expr ->
  (Action.action_v * Symbols.action * Vars.vars) list

(*------------------------------------------------------------------*)
(** {2 Action descriptions} *)

(** Return the action description associated to a shape. *)
val descr_of_shape :
  Symbols.table -> <fset:unit;..> expr -> Action.shape -> Action.descr

(** [descr_of_action table t a] returns a action description [descr]
    and a substitution [s], such that [Action.subst_descr s descr] is
    the description corresponding to the action [a] in [t]. 
    Remark: we do not apply the substitution, as it may fail by trying 
    to substitute indices by non-variable terms. *)
val descr_of_action :
  Symbols.table -> <fset:unit;..> expr -> Action.action ->
  Action.descr * Term.subst

val descrs : Symbols.table -> fset -> Action.descr System.Msh.t 

(** Iterate over all action descriptions in [system].
    Only one representative of each action shape will be passed
    to the function, with indices that are guaranteed to be fresh. *)
val iter_descrs :
  Symbols.table -> <fset:unit;..> expr -> (Action.descr -> unit) -> unit

val fold_descrs :
  (Action.descr -> 'a -> 'a) ->
  Symbols.table ->
  <fset:unit;..> expr ->
  'a ->
  'a

val map_descrs  :
  (Action.descr -> 'a) -> Symbols.table -> <fset:unit;..> expr -> 'a list

(** Pretty-print all action descriptions. *)
val pp_descrs : Symbols.table -> Format.formatter -> <fset:unit;..> expr -> unit


(*------------------------------------------------------------------*)
(** {2 Operations on finite sets} *)

(** A set containing only a single system. *)
val singleton : System.Single.t -> fset

(** Create a set expression from a non-empty list of compatible single systems.
    The list of projections must be of the same length
    as the list of systems: these projections will be used to label the
    single systems as part of the newly formed system expression.

    The table is used to check that all systems in the list are compatible.

    For example, [make_fset tbl ~labels:["left";"right"] [(s,"right");(s,"left")]]
    is an expression with two elements. Its first projection, labelled
    "left", is the right projection of [s]. *)
val make_fset :
    Symbols.table ->
    labels:Term.proj option list ->
    System.Single.t list ->
    fset

(** Finite set of all projections of a system. *)
val of_system : Symbols.table -> System.t -> fset

(** Inverse of [to_list]. Does not perform any validation. *)
val of_list : (Term.proj * System.Single.t) list -> fset

(*------------------------------------------------------------------*)
(** List of labelled elements of a set. Guaranteed to be non-empty.
    Fails if expression does not correspond to a finite set. *)
val to_list : <fset:unit;..> expr -> (Term.proj * System.Single.t) list

(** Same as [to_list], but only returns the list of projections *)
val to_projs : <fset:unit;..> expr -> Term.projs

(*------------------------------------------------------------------*)
(** Same as [to_list], but for any system expression.
    Return [None] if no projections. *)
val to_list_any : _ expr -> (Term.proj * System.Single.t) list option

(** Same as [to_list], but for any system expression.
    Return [None] if no projections. *)
val to_projs_any : _ expr -> Term.projs option

(*------------------------------------------------------------------*)
(** Project a system according to the given projections. *)
val project     : Term.projs        -> 'a expr -> 'a expr
val project_opt : Term.projs option -> 'a expr -> 'a expr

(*------------------------------------------------------------------*)
(** {2 Operations on pairs} *)

val make_pair : System.Single.t -> System.Single.t -> pair

val fst : <pair:unit;..> expr -> Term.proj * System.Single.t

val snd : <pair:unit;..> expr -> Term.proj * System.Single.t

(*------------------------------------------------------------------*)
(** {2 Contexts} *)

(** Context for interpreting global or local formulas.
    The set expression is used as default systems for interpreting
    local formulas, while the pair (when present) is used as default
    for interpreting equivalence atoms.

    It is not possible to express that an equivalence holds for all
    systems (or for all systems compatible with a given one). This
    does not seem like an important feature, and it would complexify
    the API.

    Invariant: if [pair<>None] then [set<>any]. Indeed we must ensure
    that all systems in [pair] and [set] are compatible. *)
type context = {
  set  : arbitrary ;
  pair : pair option
}

val context_any : context

(** Create context for global formulas where equivalence atoms are
    interpreted wrt the given pair, and reachability atoms are
    interpreted wrt the given set expression (default: any system
    compatible with the pair). *)
val equivalence_context : ?set:('a expr) -> <pair:unit;..> expr -> context

(** Create context for interpreting reachability formulas. *)
val reachability_context : 'a expr -> context

val pp_context : Format.formatter -> context -> unit

(** Get an expression with which all systems of a context are compatible.
    Return [None] if context is not [context_any]. *)
val get_compatible_expr : context -> compatible option

val project_set     : Term.projs        -> context -> context
val project_set_opt : Term.projs option -> context -> context

(*------------------------------------------------------------------*)
(** Make system projections compatible between two system expressions.
    Build a substitution renaming the projections of [src] using corresponding 
    projections of [dst], if any. 
    - if [strict] is [true], ensure that all systems in [src] have a corresponding
      system in [dst]. 
    - if [strict] is [false], substitution can be partial. *)
val mk_proj_subst : 
  strict:bool -> src:t  -> dst:t ->
  Term.projs option * (Term.proj * Term.proj) list

(*------------------------------------------------------------------*)
(** {2 Misc} *)
  
(** Print the system to the user. *)
val print_system : Symbols.table -> _ expr -> unit

val is_single_system : context -> bool

(*------------------------------------------------------------------*)
(** {2 Parsing, printing, and conversions} *)

module Parse : sig
  (** This module defines several kinds of expressions, they are
      all parsed from the same datatype.
      A parse item may be a system symbol or the projection of a system
      symbol and, when the item corresponds to a single system,
      it may come with an alias identifying the single system as some
      projection of the multisystem in construction. *)
  type item = {
    system     : Symbols.lsymb;
    projection : Symbols.lsymb option;
    alias      : Symbols.lsymb option
  }

  type t = item list L.located

  (** Parsing relies on [any], [any_compatible_with] and [make_fset]. *)
  val parse : Symbols.table -> t -> arbitrary

  type sys_cnt =
    | NoSystem
    | System   of t
    | Set_pair of t * t

  type sys = [`Local | `Global] * sys_cnt

  val parse_sys : Symbols.table -> sys -> context
end
