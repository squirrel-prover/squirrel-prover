(** Basic module for variables, providing local environments to store
    variables. *)

(** {2 Variables} *)

(** Type of variables of sort ['a]. *)
type 'a var

(** An [evar] is a variable of some sort. *)
type evar = EVar : 'a var -> evar

(** {3 Aliases}
  *
  * [Vars.x] is the type of variables of sort [Sorts.x]. *)

type index = Sorts.index var
type message = Sorts.message var
type boolean = Sorts.boolean var
type timestamp = Sorts.timestamp var

(** {2 Functions on variables} *)

val name : 'a var -> string

val sort : 'a var -> 'a Sorts.t

(** Print a variable, only showing its name. *)
val pp : Format.formatter -> 'a var -> unit

(** Print a list of variables, only showing their names. *)
val pp_list : Format.formatter -> 'a var list -> unit

(** Print a list of variables, showing their names and sorts. *)
val pp_typed_list : Format.formatter -> evar list -> unit

(** {2 Environments} *)

(** Local environment containg a set of variables of arbitrary sorts. *)
type env

(** Print an environment, showing variables names and sorts. *)
val pp_env : Format.formatter -> env -> unit

val empty_env : env

val to_list : env -> evar list

val of_list : evar list -> env

val mem : env -> string -> bool

exception Undefined_Variable

(** [get_var env n] returns the variable [v] in [env]
  * such that [name v = n].
  * @raise Undefined_Variable if no variable is found. *)
val get_var : env -> string -> evar

(** [rm_var env v] returns [env] minus the variable [v].
  * returns the same [env] if no variable is found. *)
val rm_var : env -> 'a var -> env


(** [make_fresh env sort prefix]
  * creates a variable of sort [sort] with a name that is not
  * already present in [env].
  * If possible the name [prefix] is used.
  * If variable of name [prefix] already exists inside the environment,
  * a variable with the given name concateneted with the smallest possible
  * integer is created.
  * The new environment and variable are returned.*)
val make_fresh : env -> 'a Sorts.t -> string -> env * 'a var

(** Same as [make_fresh], but updates the [env ref] passed as argument. *)
val make_fresh_and_update : env ref -> 'a Sorts.t -> string -> 'a var

(** Same as [make_fresh], but uses the sort and name prefix
  * of the variable passed as argument. *)
val make_fresh_from : env -> 'a var -> env * 'a var

(** Combines [make_fresh_from] and [make_fresh_and_update]. *)
val make_fresh_from_and_update : env ref -> 'a var -> 'a var
