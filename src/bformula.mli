(** Implements boolean formulas, both for terms and timestamps *)
open Term
open Atom

(** {2 Boolean formulas} *)

(** Generic type for boolean formulas *)
type 'a bformula =
  | And of 'a bformula * 'a bformula
  | Or of 'a bformula * 'a bformula
  | Not of 'a bformula
  | Impl of 'a bformula * 'a bformula
  | Atom of 'a
  | True
  | False

val pp_bformula :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a bformula -> unit

(** [atoms b] returns the list of atoms appearing in [b]. *)
val atoms : 'a bformula -> 'a list

(** Facts are boolean formulas over terms. *)

type fact = term_atom bformula

val pp_fact : Format.formatter -> fact -> unit

(** [fact_ts c] returns the timestamps appearing in [c] *)
val fact_ts : fact -> timestamp list

val subst_fact : subst -> fact -> fact

(** Replace some subformula by the result of their evaluation
  * when it is constant. *)
val triv_eval : 'a bformula -> 'a bformula

(** {2 Unquantified trace formulas} *)

(** Trace_Formula are boolean formulas over timestamps. *)

type trace_formula = trace_formula_atom bformula

val pp_trace_formula : Format.formatter -> trace_formula -> unit

(** Put a trace_formulaaint in DNF using only atoms Eq, Neq and Leq *)
val trace_formula_dnf : trace_formula -> trace_formula_atom list list

val subst_trace_formula : subst -> trace_formula -> trace_formula

(** [trace_formula_ts c] returns the timestamps appearing in [c] *)
val trace_formula_ts : trace_formula -> timestamp list
