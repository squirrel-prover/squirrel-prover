module SE = SystemExpr

module TS = LowTraceSequent
module ES = LowEquivSequent

(*------------------------------------------------------------------*)
(** A goal (in the sense of proof obligation)
    consists of one of our two kinds of sequents. *)
type t = Trace of TS.t | Equiv of ES.t

(*------------------------------------------------------------------*)
val pp : Format.formatter -> t -> unit
val pp_init : Format.formatter -> t -> unit

(*------------------------------------------------------------------*)
val vars   : t -> Vars.env
val system : t -> SE.context
val table  : t -> Symbols.table

(*------------------------------------------------------------------*)
val map      : (TS.t -> TS.t)      -> (ES.t -> ES.t)      -> t -> t
val map_list : (TS.t -> TS.t list) -> (ES.t -> ES.t list) -> t -> t list
val bind     : (TS.t -> 'a)        -> (ES.t -> 'a)        -> t -> 'a

(*------------------------------------------------------------------*)
(** Statements are formulas in context.
    They may be used to represent goals (in the sense of lemmas,
    that will then give rise to an initial proof obligation),
    axioms, or hypotheses extracted from a sequent. *)
type ('a,'b) abstract_statement = {
  name    : 'a;
  ty_vars : Type.tvars;
  system  : SE.context;
  formula : 'b;
}

(*------------------------------------------------------------------*)
type statement       = (string, Equiv.any_form) abstract_statement
type equiv_statement = (string, Equiv.form    ) abstract_statement
type reach_statement = (string, Term.term     ) abstract_statement

(*------------------------------------------------------------------*)
val pp_statement : Format.formatter -> statement -> unit

(*------------------------------------------------------------------*)
val is_reach_statement : (_, Equiv.any_form) abstract_statement -> bool
val is_equiv_statement : (_, Equiv.any_form) abstract_statement -> bool

val to_reach_statement : ?loc:Location.t -> statement -> reach_statement
val to_equiv_statement : ?loc:Location.t -> statement -> equiv_statement

(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

module Parsed : sig

  type contents =
  | Local     of Theory.term
  | Global    of Theory.global_formula
  | Obs_equiv   (** All the information is in the system expression. *)

  type t = {
    name    : Theory.lsymb option;
    ty_vars : Theory.lsymb list;
    vars    : Theory.bnds_tagged;
    system  : SE.Parse.sys;
    formula : contents
  }

end

(*------------------------------------------------------------------*)
(** {2 Create trace and equivalence goals} *)

val make_obs_equiv :
  ?enrich:Term.term list ->
  Symbols.table ->
  SE.context ->
  Equiv.any_form * t

val make : Symbols.table -> Parsed.t -> statement * t
