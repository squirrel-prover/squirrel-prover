(** Basic module for variables, providing local environments to store
    variables. *)

type 'a var

type evar = EVar : 'a var -> evar

type index = Sorts.index var
type message = Sorts.message var
type boolean = Sorts.boolean var
type timestamp = Sorts.timestamp var

val name : 'a var -> string

val var_type : 'a var -> 'a Sorts.t

val pp : Format.formatter -> 'a var -> unit

val pp_typed : Format.formatter -> 'a var -> unit

val pp_list : Format.formatter -> 'a var list -> unit

val pp_typed_list : Format.formatter -> evar list -> unit

exception Undefined_Variable

exception Variable_Already_Defined

(** Local environment containg a set of defined variables *)
type env

val pp_env : Format.formatter -> env -> unit

val empty_env : env

val to_list : env -> evar list

val mem : env -> string -> bool

(** [get_var env name] returns the variable with the given name, and raises an
    exception if it does not exists. The variable name used to match variables
    is the one obtained through [var_name]. *)
val get_var : env -> string -> evar

(** [make_fresh ?name] creates a fresh variable based on the name [name_prefix]
    if a variable with the given name already exists inside the environment, a
    variable with the given name concateneted with the smallest possible integer
    is created. The new environment and the variable are returned.*)
val make_fresh : env -> 'a Sorts.t -> string -> env * 'a var

(** Same as [make_fresh], but updates the mutable env given in input. *)
val make_fresh_and_update : env ref -> 'a Sorts.t -> string -> 'a var

val make_fresh_from : env -> 'a var -> env * 'a var

val make_fresh_from_and_update : env ref -> 'a var -> 'a var
