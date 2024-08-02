open Utils
open Ppenv

module SE = SystemExpr

module TS = LowTraceSequent
module ES = LowEquivSequent

(*------------------------------------------------------------------*)
(** A goal (in the sense of proof obligation)
    consists of one of our two kinds of sequents. *)
type t = Local of TS.t | Global of ES.t

(*------------------------------------------------------------------*)
val pp     : t formatter
val pp_dbg : t formatter
val _pp    : t formatter_p

val pp_init : t formatter_p

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
type statement        = (string, Equiv.any_form) abstract_statement
type global_statement = (string, Equiv.form    ) abstract_statement
type local_statement  = (string, Term.term     ) abstract_statement

(*------------------------------------------------------------------*)
val _pp_statement : statement formatter_p

(*------------------------------------------------------------------*)
val is_local_statement  : (_, Equiv.any_form) abstract_statement -> bool
val is_global_statement : (_, Equiv.any_form) abstract_statement -> bool

val to_local_statement  : ?loc:Location.t -> statement -> local_statement
val to_global_statement : ?loc:Location.t -> statement -> global_statement

(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

module Parsed : sig

  type contents =
  | Local     of Typing.term
  | Global    of Typing.global_formula
  | Obs_equiv   (** All the information is in the system expression. *)

  type t = {
    name    : Symbols.lsymb option;
    ty_vars : Symbols.lsymb list;
    vars    : Typing.bnds_tagged;
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
