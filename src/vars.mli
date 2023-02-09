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
      refresh variables (to avoid capture issues). 

    A variable can either represent:
    - a single computation, in which can it can only be instanciated by 
      system-independent terms. 
      This is the case for global variables.
    - many computations, in which can it can be instanciated by terms with
      diff operators and multi-system macros.
      This is the case for local variables. *)

open Utils

(*------------------------------------------------------------------*)
(** {2 Variables} *)

(** Type of variables of sort ['a]. *)
type var 

type vars = var list

(*------------------------------------------------------------------*)
(** {2 Variable scope} *)

(** A variable can have a local or global scope. *)
type scope = Local | Global

(*------------------------------------------------------------------*)
(** {2 Variable information} *)
    
module Tag : sig
  (** Variable information restricting its possible instanciations. *)
  type t = {
    const : bool;
    (** var represents a constant computation *)

    system_indep : bool;
    (** var must be instantiated by a term representiang a
        system-independent computation *)
  }

  (*------------------------------------------------------------------*)
  val pp : Format.formatter -> t -> unit

  (*------------------------------------------------------------------*)
  (** Built variable information according to the scope of a variable *)
  val make : ?const:bool -> scope -> t

  (*------------------------------------------------------------------*)
  (** default local tag *)               
  val ltag : t

  (** default global tag *)
  val gtag : t

  (*------------------------------------------------------------------*)
  (** Attached local information to a variable *)
  val local_vars : ?const:bool -> vars -> (var * t) list

  (** Attached global information to a variable *)
  val global_vars : ?const:bool -> vars -> (var * t) list
end

type tagged_var = var * Tag.t

type tagged_vars = tagged_var list

(*------------------------------------------------------------------*)
(** {2 Pretty-printing} *)

(** Print a variable, only showing its name. *)
val pp : Format.formatter -> var -> unit

(** Print a list of variables, only showing their names. *)
val pp_list : Format.formatter -> vars -> unit

(** Print a list of variables, showing their names and sorts. *)
val pp_typed_list : Format.formatter -> vars -> unit

(** Print a list of tagged variables, showing their names and sorts. *)
val pp_typed_tagged_list : Format.formatter -> tagged_vars -> unit

(*------------------------------------------------------------------*)
(** {2 Debug printing} *)
  
(** Debug versions of [pp]: also print the identifier. *)
val _pp    : dbg:bool -> Format.formatter -> var -> unit
val pp_dbg :             Format.formatter -> var -> unit

(** Debug versions of [pp_list]: also print the identifier. *)
val _pp_list    : dbg:bool -> Format.formatter -> vars -> unit
val pp_list_dbg :             Format.formatter -> vars -> unit

(** Debug versions of [pp_typed_list_dbg]: also print the identifier. *)
val _pp_typed_list    : dbg:bool -> Format.formatter -> vars -> unit
val pp_typed_list_dbg :             Format.formatter -> vars -> unit

val _pp_typed_tagged_list    : dbg:bool -> Format.formatter -> tagged_vars -> unit
val pp_typed_tagged_list_dbg :             Format.formatter -> tagged_vars -> unit
  
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
type 'a genv

(*------------------------------------------------------------------*)
type simpl_env = unit genv

type env = Tag.t genv

(*------------------------------------------------------------------*)
val get_info : var -> 'a genv -> 'a

(*------------------------------------------------------------------*)
(** Well-formedness check for **toplevel** environment.
    Check that each string corresponds to at most one variable. *)
val sanity_check : 'a genv -> unit

(*------------------------------------------------------------------*)
(** Print an environment, showing variables names and sorts. *)
val pp_genv    :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a genv -> unit

val _pp_genv    :
  dbg:bool ->
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a genv -> unit

val pp_genv_dbg :
  (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a genv -> unit

(*------------------------------------------------------------------*)
val  pp_env     :             Format.formatter -> env -> unit
val _pp_env     : dbg:bool -> Format.formatter -> env -> unit
val  pp_env_dbg :             Format.formatter -> env -> unit

(*------------------------------------------------------------------*)
val empty_env : 'a genv

(*------------------------------------------------------------------*)
val to_list      : 'a genv -> (var * 'a) list 
val to_vars_list : 'a genv -> var list 

val to_vars_set : 'a genv -> Sv.t
val to_map      : 'a genv -> 'a Mv.t 
  
(*------------------------------------------------------------------*)
val of_list : (var * 'a) list -> 'a genv
val of_map  : 'a Mv.t -> 'a genv 
val of_set  : Sv.t -> simpl_env

(*------------------------------------------------------------------*)
val to_simpl_env : 'a genv -> simpl_env
  
(*------------------------------------------------------------------*)
val mem   : 'a genv -> var -> bool
val mem_s : 'a genv -> string -> bool

(** Note: pattern variables are not uniquely characterized by a string *)
val find : 'a genv -> string -> (var * 'a) list

val add_var  : var  -> 'a      -> 'a genv -> 'a genv
val add_vars : (var * 'a) list -> 'a genv -> 'a genv

val add_var_simpl  : var  -> simpl_env -> simpl_env
val add_vars_simpl : vars -> simpl_env -> simpl_env

(** [rm_var env v] returns [env] minus the variable [v].
  * returns the same [env] if no variable is found. *)
val rm_var : var -> 'a genv -> 'a genv

val rm_vars : vars -> 'a genv -> 'a genv

(*------------------------------------------------------------------*)
val map_tag : (var -> Tag.t -> Tag.t) -> env -> env

(*------------------------------------------------------------------*)
(** {2 Create variables} *)

(*------------------------------------------------------------------*)
(** [make env sort name] creates a variable of sort [sort] in [env].
    - [~opt = `Approx], appends some suffix to [name] to get a new variable.
    - [~opt = `Shadow], uses [name], and shadows any pre-existing definition. *)
val make : 
  ?allow_pat:bool -> [`Approx | `Shadow] -> 
  'a genv -> Type.ty -> string -> 'a -> 'a genv * var

(** Make a local variable *)
val make_local : 
  ?allow_pat:bool -> [`Approx | `Shadow] -> 
  env -> Type.ty -> string -> env * var

(** Make a global variable *)
val make_global : 
  ?allow_pat:bool -> [`Approx | `Shadow] -> 
  env -> Type.ty -> string -> env * var

(*------------------------------------------------------------------*)
(** Same than [make], but uses the exact name *)
val make_exact : 'a genv -> Type.ty -> string -> 'a -> ('a genv * var) option

(*------------------------------------------------------------------*)
(** Create a new variable whose name resemble the one given in argument.  *)
val make_approx : 'a genv -> var -> 'a -> 'a genv * var

(** Stateful version of [make_approx]. *)
val make_approx_r : 'a genv ref -> var -> 'a -> var

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


