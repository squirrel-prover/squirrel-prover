(** Basic module for variables, providing local environments to store
    variables. *)

open Utils

(*------------------------------------------------------------------*)
(** {2 Variables} *)

(** Type of variables of sort ['a]. *)
type var 

type vars = var list

(*------------------------------------------------------------------*)
(** {2 Pretty-Printing} *)
  
(** Print a variable, only showing its name. *)
val pp : Format.formatter -> var -> unit

(** Print a list of variables, only showing their names. *)
val pp_list : Format.formatter -> var list -> unit

(** Print a list of variables, showing their names and sorts. *)
val pp_typed_list : Format.formatter -> var list -> unit

(*------------------------------------------------------------------*)
(** {2 Functions on variables} *)

val hash : var -> int

val name : var -> string

val ty : var -> Type.ty

val norm_ty : Type.Infer.env -> var -> var

val tsubst  : Type.tsubst -> var -> var

val equal : var -> var -> bool

(** Time-consistent: if [v] was created before [v'], then [compare v v' ≤ 0]. *)
val compare : var -> var -> int

val check_type_vars : vars -> Type.ty list -> (unit -> unit) -> unit

(** Check if a variable is a pattern hole. *)
val is_pat : var -> bool

(*------------------------------------------------------------------*)
(** {2 Set and Maps} *)

module Sv : sig 
  include Set.S with type elt = var

  val hash : t -> int

  val add_list : t -> var list -> t

  val of_list1 : var list -> t
end

module Mv : Map.S with type key = var

(*------------------------------------------------------------------*)
(** {2 Environments} *)

(** Local environment containg a set of variables of arbitrary sorts. *)
type env

val hash_env : env -> int

(** Print an environment, showing variables names and sorts. *)
val pp_env : Format.formatter -> env -> unit

val empty_env : env

val to_list : env -> var list
val to_set  : env -> Sv.t

val of_list : var list -> env
val of_set  : Sv.t -> env

val mem   : env -> var -> bool
val mem_s : env -> string -> bool

(** Note: pattern variables are not uniquely characterized by a string *)
val find : env -> string -> var list

val add_var  : var  -> env -> env
val add_vars : vars -> env -> env

(** [rm_var env v] returns [env] minus the variable [v].
  * returns the same [env] if no variable is found. *)
val rm_var : var -> env -> env

val rm_vars : vars -> env ->  env

(*------------------------------------------------------------------*)
(** {2 Create variables} *)

(** [make_new_from v] generates a new variable of the same sort as
  * [v] guaranteed to not appear anywhere else so far.
  *
  * The variables generated in this way are not meant to be seen by
  * the user. *)
val make_new_from : var -> var
val make_new : Type.ty -> string -> var

(*------------------------------------------------------------------*)
(** [make env sort name] creates a variable of sort [sort] in [env].
    - [~opt = `Approx], appends some suffix to [name] to get a new variable.
    - [~opt = `Shadow], uses [name], and shadows any pre-existing definition. *)
val make : 
  ?allow_pat:bool -> [`Approx | `Shadow] -> 
  env -> Type.ty -> string -> env * var

(*------------------------------------------------------------------*)
(** Same than [make], but uses the exact name *)
val make_exact : env -> Type.ty -> string -> (env * var) option

(*------------------------------------------------------------------*)
(** Create a fresh variable resembling the one given in argument. *)
val fresh : env -> var -> env * var

(** Stateful version of [refresh]. *)
val fresh_r : env ref -> var -> var


