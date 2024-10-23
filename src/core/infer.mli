(** Type and system variable inference.
    
    This API is **STATEFUL**.

    This module allows to create inference environment of type [env].

    Then, new variables to be inferred can be created, using:
    - [mk_ty_univar] creates a type unification variable;

    - [mk_se_univar] creates a system expression unification variable,
      which comes with optional instantiation constraints.

    Equality constraints on unification variables can be added using
    [unify_*].

    Expressions (types or systems) can be normalized using the
    [norm_*] functions. 

    Eventually, we can check whether all unification variables have
    been properly inferred and close to inference environment using
    [close], which returns (if it succeeds) a substitution of Ocaml
    type [Subst.t] from inferred unification variables to their
    inferred values. *)

(*------------------------------------------------------------------*)
open Utils

module SE = SystemExprSyntax

(*------------------------------------------------------------------*)
type env

val pp : env formatter

val mk_env : unit -> env

(*------------------------------------------------------------------*)
(** Stateful copie and set. *)
val copy : env -> env
val set : tgt:env -> value:env -> unit

(*------------------------------------------------------------------*)
(** Create a type unification to be inferred. *)
val mk_ty_univar : env -> Type.univar

(** Create a system expression variable to be inferred.

    Optionally, the variable may be restricted to be instantiated by
    a system expression satisfying [constraints].  *)
val mk_se_univar : ?constraints:SE.Var.info list -> env -> SE.Var.t

(*------------------------------------------------------------------*)
val open_tvars  : ?subst:Subst.t -> env -> Type.tvars     -> Type.univars  * Subst.t
val open_svars  : ?subst:Subst.t -> env -> SE.tagged_vars -> SE.Var.t list * Subst.t

val open_params : env -> Params.t -> Params.Open.t * Subst.t

(*------------------------------------------------------------------*)
val norm_ty         : env -> Type.ty    -> Type.ty
val norm_se         : env -> SE.t       -> SE.t
val norm_se_context : env -> SE.context -> SE.context
val norm_var        : env -> Vars.var   -> Vars.var

(*------------------------------------------------------------------*)
val unify_ty         : env -> Type.ty    -> Type.ty    -> [`Fail | `Ok]
val unify_se         : env -> SE.t       -> SE.t       -> [`Fail | `Ok]
val unify_se_context : env -> SE.context -> SE.context -> [`Fail | `Ok] 

(*------------------------------------------------------------------*)
type 'a result =
  | FreeTyVars
  | FreeSystemVars
  | BadInstantiation of (Format.formatter -> unit)
  | Closed of 'a

(** Print the error message in a result. 
    Requires that the result is **not** successful.  *)
val pp_error_result : 'a result formatter

(** [check_se_subst env v se c] check that the substitution [v → se]
    satisfies the constraints [c] in environment [env]. *)
val check_se_subst :
  Env.t -> SE.Var.t -> SE.t -> SE.Var.info list ->
  [`Ok | `BadInst of Format.formatter -> unit]

(** Try to close an inference environment, and return the closing
    substitution in case of success.
    In case of failure, return why the environment could not be closed. *)
val close : Env.t -> env -> Subst.t result

(** Similar to [close], except that it generalizes remaining type and
    system expression variables.
    Thus, [gen_and_close] cannot return [FreeTyVars] nor [FreeSystemVars]. *)
val gen_and_close : Env.t -> env -> (Params.t * Subst.t) result

(*------------------------------------------------------------------*)
(** Return the substitution associated to an inference environment.

    Does **not** check that the environment is closed, nor that the
    substitution is valid (e.g. this function does not verify that the
    system expressions satisfy the required constraints).

    Useful for printing. *)
val unsafe_to_subst : env -> Subst.t 
