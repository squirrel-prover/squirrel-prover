(** Type and system variable inference
    
    Stateful API *)

(*------------------------------------------------------------------*)
open Utils

module SE = SystemExprSyntax

(*------------------------------------------------------------------*)
type env

val pp : env formatter

val mk_env : unit -> env

(*------------------------------------------------------------------*)
val copy : env -> env
val set : tgt:env -> value:env -> unit

(*------------------------------------------------------------------*)
val mk_ty_univar : env -> Type.univar
val mk_se_univar : env -> SE.Var.t

val open_tvars : env -> Type.tvars -> Type.univars * Subst.t

val norm_ty : env -> Type.ty -> Type.ty
val norm_se : env -> SE.t    -> SE.t

val unify_eq  : env -> Type.ty -> Type.ty -> [`Fail | `Ok]

val is_closed     : env -> bool
val close         : env -> Subst.t
val gen_and_close : env -> Type.tvars * Subst.t
