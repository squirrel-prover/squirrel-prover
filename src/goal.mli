module TS = LowTraceSequent
module ES = LowEquivSequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** A goal consists of one of our two kinds of sequents. *)
type t = Trace of TS.t | Equiv of ES.t

val pp : Format.formatter -> t -> unit
val pp_init : Format.formatter -> t -> unit

val get_env : t -> Vars.env

(*------------------------------------------------------------------*)
val map      : (TS.t -> TS.t)      -> (ES.t -> ES.t)      -> t -> t
val map_list : (TS.t -> TS.t list) -> (ES.t -> ES.t list) -> t -> t list
val bind     : (TS.t -> 'a)        -> (ES.t -> 'a)        -> t -> 'a
  
(*------------------------------------------------------------------*)
(** Statements are formulas in context.
  * They may be used to generate initial goals, or to represent
  * hypotheses extracted from a goal.
  * TODO currently free variables used in axioms and lemmas are
  * quantified in the formula, but this will break when we
  * properly forbid quantification over messages in local meta-formulas. *)
type ('a,'b) abstract_statement = {
  name    : 'a;
  ty_vars : Type.tvars;
  system  : SystemExpr.t;
  formula : 'b;
}

(*------------------------------------------------------------------*)
type       statement = (string,  Equiv.gform) abstract_statement
type equiv_statement = (string,   Equiv.form) abstract_statement
type reach_statement = (string, Term.message) abstract_statement

(*------------------------------------------------------------------*)
val is_reach_statement : statement -> bool
val is_equiv_statement : statement -> bool

val to_reach_statement : ?loc:Location.t -> statement -> reach_statement
val to_equiv_statement : ?loc:Location.t -> statement -> equiv_statement

(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

module Parsed : sig

  type contents =
  | Local     of Theory.formula
  | Global    of Theory.global_formula
  | Obs_equiv   (** All the information is in the system expression. *)

  type t = {
    name    : Theory.lsymb option;
    ty_vars : Theory.lsymb list;
    vars    : Theory.bnds;
    system  : SystemExpr.parsed;
    formula : contents
  }

end

(*------------------------------------------------------------------*)
(** {2 Create trace and equivalence goals} *)

val make :
  Symbols.table -> Hint.hint_db -> Parsed.t ->
  statement * t
