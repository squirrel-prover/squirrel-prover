(** This modules provides the types used to type variables and terms.
    The type is explicit, so that we can construct terms as GADT over it. *)

(*------------------------------------------------------------------*)
type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]

(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind

type ekind = EKind : 'a kind -> ekind

(*------------------------------------------------------------------*)
val pp_kind : Format.formatter -> 'a kind -> unit

val pp_kinde : Format.formatter -> ekind -> unit

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
type _ ty =
  (** Built-in types *)
  | Message   : message   ty
  | Boolean   : message   ty
  | Index     : index     ty
  | Timestamp : timestamp ty

  (** User-defined types *)
  | TBase     : string -> message ty
        
  (** Type variable *)
  | TVar      : tvar -> message ty

  (** Type unification variable *)
  | TUnivar   : univar -> message ty
 
(*------------------------------------------------------------------*)
type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

(*------------------------------------------------------------------*)
val pp : Format.formatter -> 'a ty -> unit

val pp_e : Format.formatter -> ety -> unit

(*------------------------------------------------------------------*)
type tmessage   = message   ty
type ttimestamp = timestamp ty
type tindex     = index     ty

(*------------------------------------------------------------------*)
(** Higher-order *)
type hty =
  | Lambda of ety list * tmessage 

val pp_ht : Format.formatter -> hty -> unit

(*------------------------------------------------------------------*)
val eboolean   : ety
val emessage   : ety
val etimestamp : ety
val eindex     : ety

val ebase : string -> ety

val kind : 'a ty -> 'a kind
   
(*------------------------------------------------------------------*)
(** Equality witness for types and kinds *)
type (_,_) type_eq = Type_eq : ('a, 'a) type_eq

(*------------------------------------------------------------------*)
(** Sub-typing relation, and return a (Ocaml) type equality witness *)
val subtype_w : 'a ty -> 'b ty -> ('a,'b) type_eq option

val subtype   : 'a ty -> 'b ty -> bool

(*------------------------------------------------------------------*)
(** Equality relation, and return a (Ocaml) type equality witness *)
val equal_w : 'a ty -> 'b ty -> ('a,'b) type_eq option
val equal   : 'a ty -> 'b ty -> bool
val eequal  :   ety ->   ety -> bool

val ht_equal : hty -> hty -> bool

val equalk_w : 'a kind -> 'b kind -> ('a,'b) type_eq option
val equalk   : 'a kind -> 'b kind -> bool
  
(*------------------------------------------------------------------*)
(** {2 Type substitution } *)

(** A substitution from unification variables to (existential) types. *)
type tsubst

val tsubst   : tsubst -> 'a ty -> 'a ty
val tsubst_e : tsubst ->   ety ->   ety

val tsubst_ht : tsubst -> hty -> hty
                                         
val tsubst_add_tvar   : tsubst -> tvar   -> tmessage -> tsubst
val tsubst_add_univar : tsubst -> univar -> tmessage -> tsubst


val tsubst_empty : tsubst
  
(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> univar

  val open_tvars : env -> tvars -> univars * tsubst

  val norm   : env -> 'a ty -> 'a ty
  val enorm  : env ->   ety ->   ety
  val htnorm : env ->   hty ->   hty
      
  val unify_eq  : env -> 'a ty -> 'b ty -> [`Fail | `Ok]
  val unify_leq : env -> 'a ty -> 'b ty -> [`Fail | `Ok]

  val is_closed : env -> bool
  val close : env -> tsubst
end


(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 

    Invariant: [fty_out] tvars and univars must be bounded by [fty_vars].
*)
type 'a ftype_g = private {
  fty_iarr : int;             (** i *)
  fty_vars : 'a list;         (** 'a₁ ... 'aₙ *)  
  fty_args : message ty list; (** τ₁ × ... × τₙ *)
  fty_out  : message ty;      (** τ *)
}

(** A [ftype] uses [tvar] for quantified type variables. *)
type ftype = tvar ftype_g

(** An opened [ftype], using [univar] for quantified type varibales *)
type ftype_op = univar ftype_g
  
val mk_ftype : int -> tvar list -> message ty list -> message ty -> ftype

(** [open_ftype fty] opens an [ftype] by refreshes its quantified 
    type variables. *)
val open_ftype : Infer.env -> ftype -> ftype_op
