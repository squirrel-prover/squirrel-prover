(** Syntax for system expressions. 
    More functions are defined in the [SystemExpr] module. *)

(*------------------------------------------------------------------*)
open Utils

(*------------------------------------------------------------------*)
module L = Location
module Single = SystemSyntax.Single

(*------------------------------------------------------------------*)
(** {2 System expression variables} *)

module Var : sig
  type t

  (*------------------------------------------------------------------*)
  type info =
    | Pair                              (** multi-system of cardinal two *)
    | Compatible_with of Symbols.system (** multi-system compatible with some system *)

  (*------------------------------------------------------------------*)
  val _pp    : dbg:bool -> t formatter
  val pp     :             t formatter
  val pp_dbg :             t formatter

  val pp_info : info formatter

  (*------------------------------------------------------------------*)
  val equal : t -> t -> bool

  val name : t -> string
    
  val of_ident : Ident.t -> t
  val to_ident : t -> Ident.t

  (*------------------------------------------------------------------*)
  (** variable corresponding to the [set] in a sequent *)
  val set  : t
  (** variable corresponding to the [pair] in a sequent *)
  val pair : t

  (*------------------------------------------------------------------*)
  (** {3 Sets and maps} *)

  module S : Set.S with type elt = t
  module M : Map.S with type key = t
end

(*------------------------------------------------------------------*)
(** A system expression variable with a list of [Var.info]s
    constraining its possible instantiation. *)
type tagged_var = Var.t * Var.info list

type tagged_vars = tagged_var list
type env = tagged_vars

val lookup_string : string -> env -> Var.t option 
val fresh_var : prefix:string -> env -> Var.t

(*------------------------------------------------------------------*)
val _pp_tagged_var    : dbg:bool -> tagged_var  formatter
val pp_tagged_var     :             tagged_var  formatter
val pp_tagged_var_dbg :             tagged_var  formatter

(*------------------------------------------------------------------*)
val _pp_tagged_vars    : dbg:bool -> tagged_vars formatter
val pp_tagged_vars     :             tagged_vars formatter
val pp_tagged_vars_dbg :             tagged_vars formatter

(*------------------------------------------------------------------*)
(** system variable binder in the surface AST *)
type p_bnd  = (string L.located * string L.located list) 
type p_bnds = p_bnd list

(*------------------------------------------------------------------*)
(** {2 System expressions} *)

(** A system expression is used to indicate to which systems a formula
    applies. Some formulas apply to any system, others apply to any number of
    systems, and equivalence formulas only make sense relative to
    a pair of systems. *)
type any_info = {
  pair : bool;
  (** if true, restricts to pair of labeled single systems. *)
  compatible_with : SystemSyntax.t option
  (** if [Some s], restricts labeled single systems compatible with [s]. *)
}

type cnt =
  | Var of Var.t
  | Any of any_info
  | List of (Projection.t * Single.t) list
  (** Each single system is identified by a label. Can be empty.
      All single systems are compatible. *)

(** exposed type for system expressions *)
type exposed = {
  cnt  : cnt;
  name : string option;         (** optional short name, for printing *)
}

(** Expressions denoting sets of single systems.
    When a local formula is annotated with one such expression
    it means that it holds for all systems in the set.

    An [arbitrary expr] can be any set, in practice we use it only
    to denote the set of all systems.

    A [compatible expr] denotes a set of compatible systems,
    which makes it possible to interpret formulas with actions.

    Formulas with macros can only be interpreted in finite sets,
    represented by an [fset expr]. These sets are actually labelled
    and ordered.

    An equivalence must be annotated with a [pair expr], representing
    an ordered and labelled pair. *)
type +'a expr = private exposed

(** Hierarchy of subtypes used as phantom types. *)
type arbitrary  = < > expr
type compatible = < symbols : unit > expr
type fset       = < symbols : unit ; fset : unit > expr
type pair       = < symbols : unit ; fset : unit ; pair : unit > expr

type t = arbitrary

(*------------------------------------------------------------------*)
(** not type-safe *)
val force  : exposed -> 'b expr
val force0 : 'a expr -> 'b expr

(*------------------------------------------------------------------*)
val hash : 'a expr -> int

val pp : 'a expr formatter

val equal0 : 'a expr -> 'a expr -> bool

(*------------------------------------------------------------------*)
(** System expression denoting all possible systems:
    - [pair]: if true, restricts to pair of labeled single systems.
    - if [compatible_with = Some s], restricts labeled single systems
      compatible with [s]. *)
val any : compatible_with:SystemSyntax.t option -> pair:bool -> arbitrary

(** [full_any] is [any ~compatible_with:None ~pair:false]. *)
val full_any : arbitrary

(** Create a system expression from a system expression variable. *)
val var : Var.t -> arbitrary

(*------------------------------------------------------------------*)
val is_var  :                'a expr -> bool
val is_fset :                'a expr -> bool
val is_any  :                'a expr -> bool
val is_pair : ?se_env:env -> 'a expr -> bool

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type error_i =
  | Invalid_projection
  | Missing_projection
  | Incompatible_systems
  | Expected_compatible
  | Expected_fset
  | Expected_pair

type error = L.t option * error_i

exception Error of error

val pp_error :
  (Format.formatter -> L.t option -> unit) ->
  Format.formatter -> error -> unit

val error : ?loc:L.t -> error_i -> 'a

(*------------------------------------------------------------------*)
(** {2 Conversions} *)

(** Cast expr to arbitrary. Always succeeds. *)
val to_arbitrary : 'a expr -> arbitrary

(** Convert an expression [s] to a [compatible]. Always succeed. *)
val to_compatible : 'a expr -> compatible

(** Convert an expression [s] to a [fset].
    [s] must be convertible.

    DEPRECATED: @raise Expected_fset if the expression is not
    convertible *)
val to_fset : 'a expr -> fset

(** Convert an expression [s] to a [pair].
    [s] must be convertible. *)
val to_pair : ?se_env:env -> 'a expr -> pair

(*------------------------------------------------------------------*)
(** {2 Operations on finite sets} *)

(** A set containing only a single system. *)
val singleton : Single.t -> fset

(** Inverse of [to_list]. Does not perform any validation. *)
val of_list : (Projection.t * Single.t) list -> fset

(*------------------------------------------------------------------*)
(** List of labelled elements of a set.
    Fails if expression does not correspond to a finite set. *)
val to_list : <fset:unit;..> expr -> (Projection.t * Single.t) list

(** Same as [to_list], but only returns the list of projections *)
val to_projs : <fset:unit;..> expr -> Projection.t list

(*------------------------------------------------------------------*)
(** Same as [to_list], but for any system expression.
    Return [None] if no projections. *)
val to_list_any : _ expr -> (Projection.t * Single.t) list option

(** Same as [to_list], but for any system expression.
    Return [None] if no projections. *)
val to_projs_any : _ expr -> Projection.t list option

(*------------------------------------------------------------------*)
(** Project a system according to the given projections. *)
val project     : Projection.t list        -> 'a expr -> 'a expr
val project_opt : Projection.t list option -> 'a expr -> 'a expr

(*------------------------------------------------------------------*)
(** {2 Operations on pairs} *)

val make_pair :
  Projection.t * Single.t ->
  Projection.t * Single.t ->
  pair

val fst : <pair:unit;..> expr -> Projection.t * Single.t

val snd : <pair:unit;..> expr -> Projection.t * Single.t

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
    that all systems in [pair] and [set] are compatible. *)
type context = {
  set  : arbitrary ;
  pair : pair option
}

val context_any : context

val equal_context0 : context -> context -> bool

(** Create context for global formulas where equivalence atoms are
    interpreted wrt the given pair, and reachability atoms are
    interpreted wrt the given set expression (default: any system
    compatible with the pair). *)
val equivalence_context : ?set:('a expr) -> <pair:unit;..> expr -> context

(** Create context for interpreting reachability formulas. *)
val reachability_context : 'a expr -> context

val pp_context : context formatter

val project_set     : Projection.t list        -> context -> context
val project_set_opt : Projection.t list option -> context -> context

(*------------------------------------------------------------------*)
(** Make system projections compatible between two system expressions.
    Build a substitution renaming the projections of [src] using corresponding
    projections of [dst], if any.
    - if [strict] is [true], ensure that all systems in [src] have a corresponding
      system in [dst].
    - if [strict] is [false], substitution can be partial. *)
val mk_proj_subst :
  strict:bool -> src:t  -> dst:t ->
  Projection.t list option * (Projection.t * Projection.t) list

(** Substitute the projection naming the single systems in a system expression.
    E.g. substituting [p] by [p0] into [p: default/q; q: default/q]
    yields [p0: default/q; q: default/q] (observe that we did not substitute
    into the single systems). *)
val subst_projs : (Projection.t * Projection.t) list -> 'a expr -> 'a expr


(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** Compute all the single systems occuring in a system context.
    Return [None] if this is cannot be done. *)
val single_systems_of_context : context -> Single.Set.t option

(** Idem as [single_systems_of_context], but for a system expression. *)
val single_systems_of_se : t -> Single.Set.t option

(*------------------------------------------------------------------*)
(** Get system that is compatible with all systems of an expresion. *)
val get_compatible_system : env -> 'a expr -> Symbols.system option 

(** Check that all systems in two expressions are compatible. *)
val compatible : Symbols.table -> env -> 'a expr -> 'b expr -> bool
