(** Basic module for variables, providing local environments to store
    variables. 

    A variable is built upon a string (used for printing) and an integer 
    identifier. This allows to have several different variables with the
    same string. 
    - in user-level terms (e.g. in a sequent), there should be only one 
      free variable associated with a given string (since the identifier 
      is not printing). 
      Note that bound variables can safely re-use a string. E.g. if `x/0` 
      is a variable with string `x` and identifier `0`, then the formula:
        `forall (x/1 : int), x/0 = x/1`
      will be correctly printed to the user (the term pretty-printer 
      takes care of renaming `x/1` into some variable `x1/???`).
    - internal intermediate terms (e.g. during matching) can safely have 
      several variables with the same string. This allows to easily 
      refresh variables (to avoid capture issues). *)

open Utils

(*------------------------------------------------------------------*)
(** {2 Variables} *)

(** Type of variables of sort ['a]. *)
type var 

type vars = var list

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

(** Print a variable, only showing its name. *)
val pp : Format.formatter -> var -> unit

(** Print a list of variables, only showing their names. *)
val pp_list : Format.formatter -> var list -> unit

(** Print a list of variables, showing their names and sorts. *)
val pp_typed_list : Format.formatter -> var list -> unit

(*------------------------------------------------------------------*)
(** {2 Debug printing} *)
  
(** Debug versions of [pp]: also print the identifier. *)
val _pp    : dbg:bool -> Format.formatter -> var -> unit
val pp_dbg :             Format.formatter -> var -> unit

(** Debug versions of [pp_list]: also print the identifier. *)
val _pp_list    : dbg:bool -> Format.formatter -> var list -> unit
val pp_list_dbg :             Format.formatter -> var list -> unit

(** Debug versions of [pp_typed_list_dbg]: also print the identifier. *)
val _pp_typed_list    : dbg:bool -> Format.formatter -> var list -> unit
val pp_typed_list_dbg :             Format.formatter -> var list -> unit

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
val  pp_env    :             Format.formatter -> env -> unit
val _pp_env    : dbg:bool -> Format.formatter -> env -> unit
val pp_env_dbg :             Format.formatter -> env -> unit

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
(** Create a new variable whose name resemble the one given in argument. *)
val make_approx : env -> var -> env * var

(** Stateful version of [make_approx]. *)
val make_approx_r : env ref -> var -> var

(*------------------------------------------------------------------*)
(** [refresh v] generates a new variable of the same type as
    [v] guaranteed to not appear anywhere else so far.
  
    The variable generated uses is referred to by the same string as 
    [v] (though with a different identifier).
    Hence such variables must not be exported to the top-level, or 
    different variables would be printed with the same string (with the 
    exception of pattern holes [_]) *)
val refresh : var -> var

(** Make a new variable with a given name. Caveats of [refresh] applies! *)
val make_fresh : Type.ty -> string -> var


