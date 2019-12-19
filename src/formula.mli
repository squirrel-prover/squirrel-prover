(** Implements first order formulas, with atoms both on terms and timestamps *)

open Vars
open Term
open Bformula

(** {2 Generic first-order formulas} *)

(** A [('a,'b) foformula] is a first-order formula with
  * atoms in ['a] and quantified variables in ['b]. *)
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

(** [foformula_to_bformula conv f] converts [f] to a [bformula],
  * using [conv] to convert its atoms at the same time. *)
val foformula_to_bformula :
  ('a -> 'b) -> ('a, 'c) foformula -> 'b Bformula.bformula

(** [bformula_to_foformula conv bf] convers [bf] to a [formula],
  * using [conv] to convert atoms at the same time. *)
val bformula_to_foformula :
  ('a -> 'b) -> 'a Bformula.bformula -> ('b, 'c) foformula

(** [foformula_vars fv_atom f] returns a list containing
  * all the variables that appear either bound (quantified) in [f],
  * or free in one of its atoms according to [fv_atom]. *)
val foformula_vars : ('a -> 'b list) -> ('a, 'b) foformula -> 'b list

(** {2 Meta-logic formulas} *)

(** Atoms of the meta-logic are either timestamp or term atoms. *)
type generic_atom =
  | Constraint of trace_formula_atom
  | Message of term_atom
  | Happens of timestamp

type formula = (generic_atom, var) foformula

val pp_formula : Format.formatter -> formula -> unit

(** Returns a list containing all variables that appear either bound
  * (quantified) or free in the formula. *)
val formula_vars : formula -> var list

(** Returns a list containing all the variables that are
  * quantified inside a formula. *)
val formula_qvars : formula -> var list

val fact_to_formula : fact -> formula

val formula_to_fact : formula -> fact

val formula_to_trace_formula : formula -> trace_formula option

(** Substitution in a formula.
    Pre-condition: [formula subst f] require that [subst]
    co-domain does not contain any variable that is bound in [f]. *)
val subst_formula : subst -> formula -> formula

(** [fresh_quantifications env f] returns a formula that is alpha-equivalent
  * to [f] but where quantified variables are fresh wrt the original
  * [!env], and it updates [env] with the declaration of these new
  * variables. *)
val fresh_quantifications : env ref -> formula -> formula
