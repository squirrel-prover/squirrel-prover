(** This module define substitution that can substitute
    - type variables [Type.univar] and [Type.tvar] *)

(* TODO: move projection and system variable substitution here *)

(*------------------------------------------------------------------*)
open Utils

module Mid = Ident.Mid

(*------------------------------------------------------------------*)
(** a substitution  *)
type t

val pp_subst : t formatter

(** a substitution function over values of type ['a] *)
type 'a substitution = t -> 'a -> 'a

(*------------------------------------------------------------------*)
(** {2 Building substitutions } *)

val empty_subst : t

val mk_subst : tvars:Type.ty Mid.t -> univars:Type.ty Mid.t -> t

(*------------------------------------------------------------------*)
val add_tvar   : t -> Type.tvar   -> Type.ty -> t
val add_univar : t -> Type.univar -> Type.ty -> t

(*------------------------------------------------------------------*)
(** {2 Substitution functions} *)

val subst_ty    : Type.ty    substitution
val subst_var   : Vars.var   substitution
val subst_ftype : Type.ftype substitution
