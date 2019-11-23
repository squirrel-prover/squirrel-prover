open Vars
open Term
open Bformula

(** {2 Formulas} *)

type generic_atom =
  | Trace of ts_atom
  | Message of term_atom

(** First order formulas *)
type ('a, 'b) foformula =
  | ForAll of ('b list) * ('a, 'b) foformula
  | Exists of ('b list) * ('a, 'b) foformula
  | And of ('a, 'b) foformula * ('a, 'b) foformula
  | Or of ('a, 'b) foformula * ('a, 'b) foformula
  | Not of ('a, 'b) foformula
  | Impl of ('a, 'b) foformula * ('a, 'b) foformula
  | Atom of 'a
  | True
  | False

exception Not_a_boolean_formula

val foformula_to_bformula :
  ('a -> 'b) -> ('a, 'c) foformula -> 'b Bformula.bformula

val bformula_to_foformula :
  ('a -> 'b) -> 'a Bformula.bformula -> ('b, 'c) foformula

val tformula_vars : ('a -> 'b list) -> ('a, 'b) foformula -> 'b list

type formula = (generic_atom, var) foformula

val pp_formula : Format.formatter -> formula -> unit

val formula_vars : formula -> var list

val fact_to_formula : fact -> formula

(** Substitution in a formula.
    Pre-condition: [formula subst f] require that [subst]
    co-domain is fresh in [f]. *)
val subst_formula : subst -> formula -> formula

(** [fresh_formula env p] instantiates [p] with fresh variables for
    all variables. *)
val fresh_formula : env ref -> formula ->  formula


