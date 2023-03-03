(** This modules provides the types used to type variables and terms. *)

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar
type tvars = tvar list

val pp_tvar     : Format.formatter -> tvar -> unit
val pp_tvar_dbg : Format.formatter -> tvar -> unit

val mk_tvar : string -> tvar
val ident_of_tvar : tvar -> Ident.t
  
(*------------------------------------------------------------------*)
(** Variables for type inference *)

type univar = private Ident.t
type univars = univar list

val pp_univar : Format.formatter -> univar -> unit
  
val to_univar : Ident.t -> univar

(*------------------------------------------------------------------*)
(** Types of terms *)
type ty =
  | Message
  | Boolean
  | Index  
  | Timestamp

  | TBase of string
  (** user-defined types *)
        
  | TVar of tvar
  (** type variable *)

  | TUnivar of univar
  (** type unification variable *)

  | Tuple of ty list
  (** tuple type [t1 * ... * tn]  *)

  | Fun of ty * ty
  (** arrow type [t1 -> t2] *)

(*------------------------------------------------------------------*)
(** {2 Misc} *)

val pp : Format.formatter -> ty -> unit

(** Equality relation *)
val equal : ty -> ty -> bool

val is_tuni : ty -> bool

(*------------------------------------------------------------------*)
val free_univars      : ty      -> Ident.Sid.t 
val free_univars_list : ty list -> Ident.Sid.t 

(*------------------------------------------------------------------*)
val tboolean   : ty
val tmessage   : ty
val ttimestamp : ty
val tindex     : ty
(*------------------------------------------------------------------*)
(** {2 Type substitution } *)

(** A substitution from unification variables to (existential) types. *)
type tsubst

val pp_tsubst : Format.formatter -> tsubst -> unit

val tsubst : tsubst -> ty -> ty
                                         
val tsubst_add_tvar   : tsubst -> tvar   -> ty -> tsubst
val tsubst_add_univar : tsubst -> univar -> ty -> tsubst

val tsubst_empty : tsubst
  
(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val pp : Format.formatter -> env -> unit

  val mk_env : unit -> env

  val copy : env -> env
  val set : tgt:env -> value:env -> unit
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> ty  -> ty
      
  val unify_eq  : env -> ty -> ty -> [`Fail | `Ok]

  val is_closed     : env -> bool
  val close         : env -> tsubst
  val gen_and_close : env -> tvars * tsubst
end

(*------------------------------------------------------------------*)
(** {2 Constructors and destructors} *)
val base : string -> ty   

val fun_l : ty list -> ty -> ty

val tuple : ty list -> ty
  
(*------------------------------------------------------------------*)
(** Destruct a given number of [Fun]. 
    If [ty_env] is not [None], may add new type equalities to do so. *)
val destr_funs     : ?ty_env:Infer.env -> ty -> int -> ty list * ty
val destr_funs_opt : ?ty_env:Infer.env -> ty -> int -> (ty list * ty) option

(** If [decompose_funs t = (targs, tout)] then:
    - [t = t1 -> ... -> tn -> tout] where [targs = \[t1; ...; tn\]]
    - [tout] is not an arrow type *)
val decompose_funs : ty -> ty list * ty

(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol: 
    ∀'a₁ ... 'aₙ, τ₁ → ... → τₙ → τ *)
type 'a ftype_g = private {
  fty_vars : 'a list; (** 'a₁ ... 'aₙ *)  
  fty_args : ty list; (** τ₁, ... ,τₙ *)
  fty_out  : ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g

(*------------------------------------------------------------------*)
val pp_ftype    : Format.formatter -> ftype    -> unit
val pp_ftype_op : Format.formatter -> ftype_op -> unit

(*------------------------------------------------------------------*)
val ftype_free_univars : ftype -> Ident.Sid.t
 
val tsubst_ftype : tsubst -> ftype -> ftype 

(*------------------------------------------------------------------*)
val mk_ftype : tvar list -> ty list -> ty -> ftype

(** Declare a function of arity one (all arguments are grouped 
    into a tuple). *)
val mk_ftype_tuple : tvar list -> ty list -> ty -> ftype

(*------------------------------------------------------------------*)
(** [open_ftype fty] opens an [ftype] by refreshes its quantified 
    type variables. *)
val open_ftype : Infer.env -> ftype -> ftype_op
