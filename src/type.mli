(** This modules provides the types used to type variables and terms.
    The type is explicit, so that we can construct terms as GADT over it. *)


type message   = [`Message]
type index     = [`Index]
type timestamp = [`Timestamp]
type boolean   = [`Boolean]
type unknown   = [`Unknown]

(*------------------------------------------------------------------*)
(** Kinds of types *)
type _ kind =
  | KMessage   : message   kind
  | KBoolean   : boolean   kind
  | KIndex     : index     kind
  | KTimestamp : timestamp kind
  | KUnknown   : unknown   kind (* for type inference variable *)

(*------------------------------------------------------------------*)
(** Variable for type inference *)
type univar

val pp_univar : Format.formatter -> univar -> unit
  
(*------------------------------------------------------------------*)
(** Types of terms *)
type _ ty =
  (** Built-in types *)
  | Message   : message   ty
  | Boolean   : boolean   ty
  | Index     : index     ty
  | Timestamp : timestamp ty

  (** User-defined types *)
  | TBase   : string  -> message ty
        
  (** Type variable *)
  | TVar    : Ident.t -> message ty

  (** Type unification variable *)
  | TUnivar : univar  -> unknown ty

(*------------------------------------------------------------------*)
type 'a t = 'a ty

type ety = ETy : 'a ty -> ety

(*------------------------------------------------------------------*)
val eboolean   : ety
val emessage   : ety
val etimestamp : ety
val eindex     : ety

val ebase : string  -> ety
val etvar : Ident.t -> ety

val kind : 'a ty -> 'a kind
   
(*------------------------------------------------------------------*)
(** Equality witness for kinds *)
type (_,_) kind_eq = Kind_eq : ('a, 'a) kind_eq

(** Equality witness for types *)
type (_,_) type_eq = Type_eq : ('a, 'a) type_eq

(*------------------------------------------------------------------*)
(** Sub-typing relation, and return a (Ocaml) type equality witness *)
val subtype_w : 'a ty -> 'b ty -> ('a,'b) type_eq option

val subtype   : 'a ty -> 'b ty -> bool

(*------------------------------------------------------------------*)
(** Equality relation, and return a (Ocaml) type equality witness *)
val equal_w : 'a ty -> 'b ty -> ('a,'b) type_eq option

val equal   : 'a ty -> 'b ty -> bool

(*------------------------------------------------------------------*)
val pp : Format.formatter -> 'a ty -> unit

val pp_e : Format.formatter -> ety -> unit

(*------------------------------------------------------------------*)
(** {2 Function symbols type} *)

(** Type of a function symbol of index arity i: 
    ∀'a₁ ... 'aₙ, τ₁ × ... × τₙ → τ 
*)
type ftype = {
  fty_iarr : int;          (** i *)
  fty_vars : Ident.t list; (** a₁ ... 'aₙ *)  
  fty_args : ety list;     (** τ₁ × ... × τₙ *)
  fty_out  : ety;          (** τ *)
}

val mk_ftype : int -> Ident.t list -> ety list -> ety -> ftype

(*------------------------------------------------------------------*)
(** {2 Type substitution } *)

(** A substitution from unification variables to (existential) types. *)
type tsubst = univar -> ety

(*------------------------------------------------------------------*)
(** {2 Type inference } *)

(** Stateful API *)
module Infer : sig
  type env

  val mk_env : unit -> env
    
  val mk_univar : env -> ety
                         
  val unify_eq  : env -> ety -> ety -> [`Fail | `Ok]
  val unify_leq : env -> ety -> ety -> [`Fail | `Ok]

  val is_closed : env -> bool
  val close : env -> tsubst
end
