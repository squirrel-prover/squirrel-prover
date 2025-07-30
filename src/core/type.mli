(** This modules provides the types used to type variables and terms. *)

open Utils

(*------------------------------------------------------------------*)
module Mid = Ident.Mid
module Sid = Ident.Sid

(*------------------------------------------------------------------*)
(** Type variables *)

type tvar = Ident.t
type tvars = tvar list

val _pp_tvar    : dbg:bool -> tvar formatter
val pp_tvar     :             tvar formatter
val pp_tvar_dbg :             tvar formatter

val mk_tvar : string -> tvar
  
(*------------------------------------------------------------------*)
(** Variables for type inference *)

type univar = Ident.t
type univars = univar list

val pp_univar : univar formatter

(*------------------------------------------------------------------*)
(** An untyped path of the form (namespace path, name) *)
type s_path = string list * string

(** Types of terms *)
type ty = private
  | Message
  | Boolean
  | Index  
  | Timestamp

  (* FIXME: use a type-safe [Symbols.path] *)
  | TConstr of s_path * ty list
  (** user-defined type constructor (path, args) *)
        
  | TVar of tvar
  (** type variable *)

  | TUnivar of univar
  (** type unification variable *)

  | Tuple of ty list
  (** tuple type [t1 * ... * tn]  *)

  | Fun of ty * ty
  (** arrow type [t1 -> t2] *)

(*------------------------------------------------------------------*)
(** {2 Iterators, do not recurse} *)
           
val map_fold : (ty -> 'a -> ty * 'a) -> ty -> 'a -> ty * 'a 
val map      : (ty ->            ty) -> ty       -> ty
val fold     : (ty -> 'a ->      'a) -> ty -> 'a -> 'a
val iter     : (ty ->          unit) -> ty       -> unit
val forall   : (ty ->          bool) -> ty       -> bool
val exists   : (ty ->          bool) -> ty       -> bool
    
(*------------------------------------------------------------------*)
(** {2 Misc} *)

val pp     :             ty formatter
val pp_dbg :             ty formatter
val _pp    : dbg:bool -> ty formatter

(** Encoding of a type as a string without discontinuity nor
    parenthesis. *)
val to_string : ty -> string

(** Short name, based on the type (for automatic variable naming) *)
val short_name : ty -> string

(** Equality relation *)
val equal : ty -> ty -> bool

val contains_tuni : ty -> bool

(*------------------------------------------------------------------*)
(** Free variables in types *)

module Fv : sig
  type t = { tv : Sid.t; uv : Sid.t; }

  val pp : t formatter

  val empty : t
  val union : t -> t -> t
  val diff : t -> t -> t

  val add_tv : univar -> t -> t
  val add_uv : univar -> t -> t

  val rem_tv : tvar   -> t -> t
  val rem_uv : univar -> t -> t

  val rem_tvs : tvar   list -> t -> t
  val rem_uvs : univar list -> t -> t
end

(*------------------------------------------------------------------*)
val fv  : ty      -> Fv.t
val fvs : ty list -> Fv.t
 
(*------------------------------------------------------------------*)
(** {2 Constructors and destructors} *)

(*------------------------------------------------------------------*)
val tboolean   : ty
val tmessage   : ty
val ttimestamp : ty
val tindex     : ty

(** unit is an alias for the 0-ary tuple *)
val tunit : ty

(*------------------------------------------------------------------*)
(** Prelude types *)

val of_s_path : ?args:ty list -> (string list * string) -> ty

(*------------------------------------------------------------------*)
val tquantum_message : ty
val tmeasure_rnd     : ty
val tint             : ty
val tstring          : ty


(*------------------------------------------------------------------*)
val univar : univar                -> ty
val tvar   : tvar                  -> ty
val func   : ty          -> ty     -> ty
val fun_l  : ty list     -> ty     -> ty
val tuple  : ty list     -> ty

(** Check if a type is definitely classical *)
val is_classical_type : ty -> bool

(** Check if a type is definitely quantum *)
val is_quantum_type : ty -> bool

(*------------------------------------------------------------------*)  
(** If [decompose_funs t = (targs, tout)] then:
    - [t = t1 -> ... -> tn -> tout] where [targs = \[t1; ...; tn\]]
    - [tout] is not an arrow type *)
val decompose_funs : ty -> ty list * ty

(** If [decompose_tuple ty = l] then either:
    - [List.length l = 1] and [l = [ty]]
    - or [ty = Tuple t]. *)
val decompose_tuple : ty -> ty list

(*------------------------------------------------------------------*)
val is_tuple : ty -> bool

(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol: 
    ∀'a₁ ... 'aₙ, τ₁ → ... → τₙ → τ *)
type 'a ftype_g = {
  fty_vars : 'a list; (** 'a₁ ... 'aₙ *)  
  fty_args : ty list; (** τ₁, ... ,τₙ *)
  fty_out  : ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g

(*------------------------------------------------------------------*)
val pp_ftype    : ftype    formatter
val pp_ftype_op : ftype_op formatter

(*------------------------------------------------------------------*)
val ftype_fv : ftype -> Fv.t
 
(*------------------------------------------------------------------*)
val mk_ftype : 'a list -> ty list -> ty -> 'a ftype_g
  
(** Declare a function of arity one (all arguments are grouped 
    into a tuple). *)
val mk_ftype_tuple : tvar list -> ty list -> ty -> ftype
