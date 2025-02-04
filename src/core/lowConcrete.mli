open Utils
open Ppenv

module SE = SystemExpr
module Sv = Vars.Sv

(*------------------------------------------------------------------*)
type bound =
  | Glob                   (** a global proof-term *)
  | ReachAsym              (** a local asymptotic proof-term *)
  | ReachConc of Term.term (** a local concrete proof-term *)

(*------------------------------------------------------------------*)
val _pp    : bound formatter_p
val pp     : bound formatter
val pp_dbg : bound formatter

(*------------------------------------------------------------------*)
val equal : bound -> bound -> bool

val fv : bound -> Sv.t

val subst  : Term.subst -> bound -> bound
val gsubst : Subst.t    -> bound -> bound

(*------------------------------------------------------------------*)
val bound_projs : Projection.t list -> bound -> bound
val bound_subst_projs :
  (Projection.t * Projection.t) list -> bound -> bound

(*------------------------------------------------------------------*)
val get : bound -> Term.term
val map_term : (Term.term -> Term.term) -> bound -> bound

(*------------------------------------------------------------------*)
val from_option : ?conc:bound -> Term.term option -> bound
val to_option : bound -> Term.term option

(*------------------------------------------------------------------*)
val is_zero : Symbols.table -> bound -> bool
val is_asym : Symbols.table -> bound -> bool
val is_concrete : bound -> bool

(*------------------------------------------------------------------*)
val ge_zero : Symbols.table -> bound -> bool

(*------------------------------------------------------------------*)
val entails :
  Symbols.table -> SE.context -> bound -> bound -> bool

