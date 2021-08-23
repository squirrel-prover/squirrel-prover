(** Basic module for variables, providing local environments to store
    variables. *)

(*------------------------------------------------------------------*)
(** {2 Variables} *)

(** Type of variables of sort ['a]. *)
type 'a var 

type 'a vars = 'a var list

(** An [evar] is a variable of some sort. *)
type evar = EVar : 'a var -> evar

type evars = evar list

val evar : 'a var -> evar

(** {3 Aliases}
  *
  * [Vars.x] is the type of variables of sort [Type.x]. *)

type index     = Type.index     var
type message   = Type.message   var
type boolean   = Type.message   var
type timestamp = Type.timestamp var

(*------------------------------------------------------------------*)
(** {2 Pretty-Printing} *)
  
(** Print a variable, only showing its name. *)
val pp   : Format.formatter -> 'a var -> unit
val pp_e : Format.formatter ->   evar -> unit

(** Print a list of variables, only showing their names. *)
val pp_list : Format.formatter -> 'a var list -> unit

(** Print a list of variables, showing their names and sorts. *)
val pp_typed_list : Format.formatter -> evar list -> unit

(*------------------------------------------------------------------*)
(** {2 Functions on variables} *)

val hash : 'a var -> int
val ehash : evar -> int

val name : 'a var -> string

val ty : 'a var -> 'a Type.ty
val ety : evar -> Type.ety

val norm_ty  : Type.Infer.env -> 'a var -> 'a var
val enorm_ty : Type.Infer.env ->   evar ->   evar

val tsubst   : Type.tsubst -> 'a var -> 'a var
val tsubst_e : Type.tsubst ->   evar ->   evar

val kind : 'a var -> 'a Type.kind

exception CastError

val cast  : 'a var -> 'b Type.kind -> 'b var
val ecast :   evar -> 'a Type.kind -> 'a var

val equal : 'a var -> 'b var -> bool

(** Time-consistent: if [v] was created before [v'], then [compare v v' ≤ 0]. *)
val compare : 'a var -> 'b var -> int


(*------------------------------------------------------------------*)
(** {2 Set and Maps} *)

module Sv : sig 
  include Set.S with type elt = evar

  val hash : t -> int

  val add_list : t -> 'a var list -> t

  val of_list1 : 'a var list -> t
end

module Mv : Map.S with type key = evar

(*------------------------------------------------------------------*)
(** {2 Environments} *)

(** Local environment containg a set of variables of arbitrary sorts. *)
type env

val hash_env : env -> int

(** Print an environment, showing variables names and sorts. *)
val pp_env : Format.formatter -> env -> unit

val empty_env : env

val to_list : env -> evar list
val to_set  : env -> Sv.t

val of_list : evar list -> env
val of_set  : Sv.t -> env

val mem   : env -> 'a var -> bool
val mem_e : env ->   evar -> bool
val mem_s : env -> string -> bool

(** Note: pattern variables are not uniquely characterized by a string *)
val find   : env -> string -> 'a Type.kind -> 'a var 

(** [rm_var env v] returns [env] minus the variable [v].
  * returns the same [env] if no variable is found. *)
val rm_var  : env -> 'a var -> env
val rm_evar : env ->   evar -> env

val rm_vars  : env -> 'a var list -> env
val rm_evars : env ->   evar list -> env


(*------------------------------------------------------------------*)
(** {2 Create variables} *)

(** [make_new_from v] generates a new variable of the same sort as
  * [v] guaranteed to not appear anywhere else so far.
  *
  * The variables generated in this way are not meant to be seen by
  * the user. *)
val make_new_from : 'a var -> 'a var
val make_new : 'a Type.t -> string -> 'a var

(** [is_new v] returns [true] iff variable [v] has been created
  * using [make_new_from]. *)
val is_new : 'a var -> bool

(** Check if a variable is a pattern hole. *)
val is_pat : 'a var -> bool

(** [make env sort name] creates a variable of sort [sort] in [env].
    - [~opt = `Approx], appends some suffix to [name] to get a new variable.
    - [~opt = `Shadow], uses [name], and shadows any pre-existing definition. *)
val make : 
  ?allow_pat:bool -> [`Approx | `Shadow] -> 
  env -> 'a Type.t -> string -> env * 'a var

(** Stateful version of [make] *)
val make_r : 
  ?allow_pat:bool -> [`Approx | `Shadow] -> 
  env ref -> 'a Type.t -> string -> 'a var

(** Same than [make], but uses the exact name *)
val make_exact : env -> 'a Type.t -> string -> (env * 'a var) option

(** Stateful version of [make_exact] *)
val make_exact_r : env ref -> 'a Type.t -> string -> 'a var option

(** Create a fresh variable resembling the one given in argument. *)
val fresh : env -> 'a var -> env * 'a var

(** Stateful version of [refresh]. *)
val fresh_r : env ref -> 'a var -> 'a var


