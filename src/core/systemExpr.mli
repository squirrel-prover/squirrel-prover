include module type of SystemExprSyntax

(*------------------------------------------------------------------*)
(** {2 General operations} *)

(** [subset s1 s2] iff [s1] is included in [s2]. *)
val subset : Symbols.table -> 'a expr -> 'a expr -> bool

(*------------------------------------------------------------------*)
(** Use equality over systems ([equal] or [equal0]) and not [Stdlib.(=)]! *)
val equal  : Symbols.table -> 'a expr -> 'a expr -> bool

(*------------------------------------------------------------------*)
(** [subset s1 s2] iff [s1] is included in [s2] modulo renaming projections *)
val subset_modulo : Symbols.table -> 'a expr -> 'a expr -> bool

val equal_modulo  : Symbols.table -> 'a expr -> 'a expr -> bool

(*------------------------------------------------------------------*)
(** {2 Operations on finite sets} *)

(** Finite set of all projections of a system. *)
val of_system : Symbols.table -> System.t -> fset

(** create the bi-system for the empty system declared in the
    [Prelude] *)
val empty_system : Symbols.table -> pair 

(** Create a set expression from a list of compatible single systems.
    The list of projections must be of the same length
    as the list of systems: these projections will be used to label the
    single systems as part of the newly formed system expression.

    The table is used to check that all systems in the list are compatible.

    For example,
    [make_fset tbl ~labels:["left";"right"] [(s,"right");(s,"left")]]
    is an expression with two elements. Its first projection, labelled
    "left", is the right projection of [s]. *)
val make_fset :
  ?loc:L.t -> 
  Symbols.table ->
  labels:Projection.t option list ->
  System.Single.t list ->
  fset

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


(*------------------------------------------------------------------*)
(** {2 Miscelaneous} *)

(** Get an expression with which all systems of a context are compatible.
    Return [None] if context is [context_any]. *)
val get_compatible_of_context : 
  Symbols.table -> env -> context -> compatible option

val gsubst         : 'a expr Subst.substitution
val gsubst_context : context Subst.substitution

(*------------------------------------------------------------------*)
(** {2 Pretty-printers} *)

(** Pretty-print all action descriptions. *)
val pp_descrs : Symbols.table -> Format.formatter -> <fset:unit;..> expr -> unit
   
(** Print the system to the user. *)
val print_system : Symbols.table -> _ expr -> unit

(*------------------------------------------------------------------*)
(** {2 Parsing} *)

module Parse : sig
  (** This module defines several kinds of expressions, they are
      all parsed from the same datatype.
      A parse item may be a system symbol or the projection of a system
      symbol and, when the item corresponds to a single system,
      it may come with an alias identifying the single system as some
      projection of the multisystem in construction. *)
  type item = {
    system     : Symbols.p_path;
    projection : Symbols.lsymb option;
    alias      : Symbols.lsymb option
  }

  type t = item list L.located

  (** Parse a system expression.
      If [implicit], then implicit system variables starting with a ['P] 
      are added to [env] during parsing, with infos [implicit_infos]. 
      If not [allow_vars], then the returned environment is exactly
      the environment given as input. *)
  val parse :
    implicit:bool ->
    ?implicit_infos:Var.info list ->
    se_env:env -> Symbols.table -> t -> env * arbitrary

  (*------------------------------------------------------------------*)
  type p_context_i =
    | NoSystem
    | System   of t
    | Set_pair of t * t

  type p_context = p_context_i L.located 

  
  (** Parse a system context for a local lemma.
      See [parse] for a description of [implicit]. *)
  val parse_local_context :
    implicit:bool ->
    se_env:env -> Symbols.table -> p_context -> env * context

  (** Same as [parse_local_context], but for a global lemma. *)
  val parse_global_context :
    implicit:bool ->
    se_env:env -> Symbols.table -> p_context -> env * context

  (*------------------------------------------------------------------*)
  type sys = [`Local | `Global] * p_context
end
