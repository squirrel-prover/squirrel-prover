(** Type and system variable inference
    
    Stateful API *)

(*------------------------------------------------------------------*)
open Utils

(*------------------------------------------------------------------*)
type env

val pp : env formatter

val mk_env : unit -> env

val copy : env -> env
val set : tgt:env -> value:env -> unit

val mk_univar : env -> Type.univar

val open_tvars : env -> Type.tvars -> Type.univars * Type.tsubst

val norm : env -> Type.ty -> Type.ty

val unify_eq  : env -> Type.ty -> Type.ty -> [`Fail | `Ok]

val is_closed     : env -> bool
val close         : env -> Type.tsubst
val gen_and_close : env -> Type.tvars * Type.tsubst
