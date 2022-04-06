(** This modules provides the types used to type variables and terms. *)

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar
type tvars = tvar list

val pp_tvar : Format.formatter -> tvar -> unit

val mk_tvar : string -> tvar
val ident_of_tvar : tvar -> Ident.t
  
(*------------------------------------------------------------------*)
(** Variables for type inference *)

type univar
type univars = univar list

val pp_univar : Format.formatter -> univar -> unit
  
(*------------------------------------------------------------------*)
(** Types of terms *)
type ty =
  (* Built-in types *)
  | Message
  | Boolean
  | Index  
  | Timestamp

  | TBase   of string
  (** User-defined types *)
        
  | TVar    of tvar
  (** Type variable *)

  | TUnivar of univar
  (** Type unification variable *)

(*------------------------------------------------------------------*)
val pp : Format.formatter -> ty -> unit

(*------------------------------------------------------------------*)
val is_tuni : ty -> bool

(** Is the type a finite type, e.g. [Index] or [Timestamp] *)
val is_finite : ty -> bool 

(*------------------------------------------------------------------*)
(** Higher-order *)
type hty = Lambda of ty list * ty

val pp_ht : Format.formatter -> hty -> unit

(*------------------------------------------------------------------*)
val tboolean   : ty
val tmessage   : ty
val ttimestamp : ty
val tindex     : ty

val base : string -> ty   

(*------------------------------------------------------------------*)
(** Sub-typing relation *)
val subtype   : ty -> ty -> bool

(*------------------------------------------------------------------*)
(** Equality relation *)
val equal : ty -> ty -> bool

val ht_equal : hty -> hty -> bool
  
(*------------------------------------------------------------------*)
(** {2 Type substitution } *)

(** A substitution from unification variables to (existential) types. *)
type tsubst

val tsubst : tsubst -> ty -> ty

val tsubst_ht : tsubst -> hty -> hty
                                         
val tsubst_add_tvar   : tsubst -> tvar   -> ty -> tsubst
val tsubst_add_univar : tsubst -> univar -> ty -> tsubst


val tsubst_empty : tsubst
  
(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> ty  -> ty
  val htnorm : env -> hty -> hty
      
  val unify_eq  : env -> ty -> ty -> [`Fail | `Ok]
  val unify_leq : env -> ty -> ty -> [`Fail | `Ok]

  val is_closed     : env -> bool
  val close         : env -> tsubst
  val gen_and_close : env -> tvars * tsubst
end

(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 

    Invariant: [fty_out] tvars and univars must be bounded by [fty_vars].
*)
type 'a ftype_g = private {
  fty_iarr : int;     (** i *)
  fty_vars : 'a list; (** 'a₁ ... 'aₙ *)  
  fty_args : ty list; (** τ₁ × ... × τₙ *)
  fty_out  : ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g
  
val mk_ftype : int -> tvar list -> ty list -> ty -> ftype

(** [open_ftype fty] opens an [ftype] by refreshes its quantified 
    type variables. *)
val open_ftype : Infer.env -> ftype -> ftype_op
