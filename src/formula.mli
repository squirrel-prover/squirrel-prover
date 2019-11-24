(** Implements first order formulas, with atoms both on terms and timestamps *)

open Vars
open Term
open Bformula

(** {2 First-order Formulas} *)

(** Atoms either for both terms and timestamps. *)
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

(** Returns all the variables appearing inside a formula. *)
val formula_vars : formula -> var list

(** Returns all the quantified varialbes appearing inside a formula. *)
val formula_qvars : formula -> var list

val fact_to_formula : fact -> formula

val is_disjunction : formula -> bool
val is_conjunction : formula -> bool

val conjunction_to_atom_lists : formula -> fact list * constr list

val disjunction_to_atom_lists : formula -> fact list * constr list

(** Substitution in a formula.
    Pre-condition: [formula subst f] require that [subst]
    co-domain is fresh in [f]. *)
val subst_formula : subst -> formula -> formula

(** [fresh_formula env p] instantiates [p] with fresh variables for
    the quantified variables. *)
val fresh_formula : env ref -> formula ->  formula


