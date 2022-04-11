(** A system expression is used to indicate to which systems a formula
    applies. Some formulas apply to any system, others apply to any number of
    systems, and equivalence formulas only make sense relative to
    a pair of systems. *)

(** We use names to identify the projections of a multi-system.
    Default strings like "left"/"right" or "1"/"2"/...
    are often used but the user may prefer to use e.g. "real"/"ideal". *)
type projection = string

(** TODO documentation *)

type unary     = [`Unary]
type binary    = [`Binary]
type arbitrary = [`Unary|`Binary|`Other]
type +'a expr
type t = arbitrary expr

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

val hash : t -> int
val pp : Format.formatter -> t -> unit

(** {2 Compatibility} TODO *)

val to_list : arbitrary expr -> unary expr list
val get_proj : unary expr -> Term.projection
val get_proj_string : unary expr -> string

(*------------------------------------------------------------------*)
(** Expressions denoting single systems. *)
module Single : sig

  type t = unary expr

  (** A single system is obtained by projecting a multi-system,
      identified by a system symbol. *)
  val make : Symbols.system Symbols.t -> projection -> t

  val pp : Format.formatter -> t -> unit

  val get_symbol : t -> Symbols.system Symbols.t

end

(*------------------------------------------------------------------*)
(** Expressions denoting sets of systems. *)
module Set : sig

  (** A system expression denoting a finite set of compatible systems,
      or the set of all systems, including those that are not yet declared.
      When a local formula is annotated with one such expression
      it means that it holds for all systems in the set. *)
  type t = arbitrary expr

  (** System expression denoting all possible systems.
      It is typically used for axioms or lemmas about primitives. *)
  val any : t

  (** Create a set expression from a non-empty list of compatible systems.
      If a list of labels is specified, it must be of the same length
      as the list of systems. *)
  val of_list : Symbols.table ->
                ?labels:string list ->
                Single.t list ->
                t

  (** Create a set expression from a system symbol. *)
  val of_symbol : Single.t list -> t

  (** [subset s1 s2] iff [s1] is included in [s2]. *)
  val subset : t -> t -> bool

end

(*------------------------------------------------------------------*)
(** Expressions denoting pairs of systems. *)
module Pair : sig

  (** A system expression denoting a pair of compatible systems. *)
  type t = binary expr

  val make : Symbols.table -> Single.t -> Single.t -> t

  val pp : Format.formatter -> t -> unit

end

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

type ssymb_pair = System.t * System.t

type system_expr_err =
  | NotABiProcess        of System.t option
  | NoneProject
  | InvalidAction        of t * Action.shape
  | IncompatibleAction   of ssymb_pair * string
  | DifferentControlFlow of ssymb_pair

val pp_system_expr_err : Format.formatter -> system_expr_err -> unit

exception System_error of system_expr_err

(*------------------------------------------------------------------*)
(** {2 Projection and action builder} *)

(** Project a system according to the given projection. The projection
    must not be None, and the system must be a bi-system.
    TODO this is for compatibility and should eventually disappear *)
val project : Term.projection -> t -> t

(** Convert action to the corresponding [Action] timestamp term in
    a system expression.
    Remark that this requires both system to declare the action,
    with the same name. *)
val action_to_term :
  Symbols.table -> t -> Action.action -> Term.term

(*------------------------------------------------------------------*)
(** {2 Action descriptions and iterators} *)

val descr_of_shape :
  Symbols.table -> t -> Action.shape -> Action.descr

(** [descr_of_action table t a] returns the description corresponding
    to the action [a] in [t].
    @raise Not_found if no action corresponds to [a]. *)
val descr_of_action :
  Symbols.table -> t -> Action.action -> Action.descr

(** Get the action symbols table of a system expression.
  * We rely on the invariant that the systems of a system expression
  * must have the same action names. *)
val symbs :
  Symbols.table ->
  t ->
  Symbols.action Symbols.t System.Msh.t

(** Iterate over all action descriptions in [system].
    Only one representative of each action shape will be passed
    to the function, with indices that are guaranteed to be fresh. *)
val iter_descrs : Symbols.table -> t -> (Action.descr -> unit) -> unit

val fold_descrs : (Action.descr -> 'a -> 'a) -> Symbols.table -> t -> 'a -> 'a
val map_descrs  : (Action.descr -> 'a)       -> Symbols.table -> t -> 'a list

(*------------------------------------------------------------------*)
(** {2 Cloning } *)

(** [clone_system_iter table sys name f] creates a copy of single system [sys]
    with each action description modified by [f] and registers it as [name].
    Fails if [name] is already in use.
    Returns the newly enriched table and [name] as a system symbol. *)
val clone_system_iter :
  Symbols.table ->
  Single.t ->
  Symbols.lsymb ->
  (Action.descr -> Action.descr) ->
  Symbols.table * Symbols.System.ns Symbols.t

(*------------------------------------------------------------------*)
(** {2 Pretty-printing } *)

(** Pretty-print all action descriptions. *)
val pp_descrs : Symbols.table -> Format.formatter -> t -> unit

(*------------------------------------------------------------------*)
(** {2 Parser types} TODO compatibility *)

type lsymb = Symbols.lsymb

val default_system_name : lsymb

type p_single_system =
  | P_Left  of lsymb
  | P_Right of lsymb

type p_system_expr_i =
  | P_Single     of p_single_system
  | P_SimplePair of lsymb
  | P_Pair       of p_single_system * p_single_system

type p_system_expr = p_system_expr_i Location.located 

val parse_single : Symbols.table -> p_single_system -> Single.t
val parse_se     : Symbols.table -> p_system_expr   -> t

val pp_p_system : Format.formatter -> p_system_expr -> unit
