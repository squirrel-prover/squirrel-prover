(** This module define substitution that can substitute
    - type variables [Type.univar] and [Type.tvar] *)

(*------------------------------------------------------------------*)
open Utils

module SE = SystemExprSyntax

module Msv = SE.Var.M
module Mid = Ident.Mid

(*------------------------------------------------------------------*)
(** a substitution  *)
type t = private {
  univars : Type.ty Mid.t; (** type unification variables *)
  tvars   : Type.ty Mid.t; (** type variables *)
  se_vars : SE.t    Msv.t; (** system expression variables *)  
}

val pp_subst : t formatter

(** a substitution function over values of type ['a] *)
type 'a substitution = t -> 'a -> 'a

(*------------------------------------------------------------------*)
(** {2 Building substitutions } *)

val empty_subst : t

val mk_subst :
  ?tvars   : Type.ty Mid.t ->
  ?univars : Type.ty Mid.t ->
  ?se_vars : SE.t    Msv.t ->
  unit -> t

(*------------------------------------------------------------------*)
val add_tvar   : t -> Type.tvar   -> Type.ty -> t
val add_univar : t -> Type.univar -> Type.ty -> t
val add_se_var : t -> SE.Var.t    -> SE.t    -> t

(*------------------------------------------------------------------*)
(** {2 Substitution functions} *)

val subst_se_var : t -> SE.Var.t -> SE.t

val subst_ty     : Type.ty    substitution
val subst_var    : Vars.var   substitution
val subst_ftype  : Type.ftype substitution
