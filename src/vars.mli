(** Basic module for variables, providing local environments to store
    variables. *)

type sort =  Message | Boolean | Index | Timestamp

val pp_type : Format.formatter -> sort -> unit

type var

val name : var -> string

val var_type : var -> sort

val pp : Format.formatter -> var -> unit

val pp_typed : Format.formatter -> var -> unit

val pp_list : Format.formatter -> var list -> unit

val pp_typed_list : string -> Format.formatter -> var list -> unit

exception Undefined_Variable

exception Variable_Already_Defined

(** Local environment containg a set of defined variables *)
type env

val pp_env : Format.formatter -> env -> unit

val pp_typed_env : Format.formatter -> env -> unit

val empty_env : env

val to_list : env -> var list

val mem : env -> string -> bool

(** [get_var env name] returns the variable with the given name, and raises an
    exception if it does not exists. The variable name used to match variables
    is the one obtained through [var_name]. *)
val get_var : env -> string -> var

(** [make_fresh ?name] creates a fresh variable based on the name [name_prefix]
    if a variable with the given name already exists inside the environment, a
    variable with the given name concateneted with the smallest possible integer
    is created. The new environment and the variable are returned.*)
val make_fresh : env -> sort -> string -> env * var

(** Same as [make_fresh], but updates the mutable env given in input. *)
val make_fresh_and_update : env ref -> sort -> string -> var

val make_fresh_from : env -> var -> env * var

val make_fresh_from_and_update : env ref -> var -> var
