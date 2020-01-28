(** Implements first order formulas, with atoms both on terms and timestamps *)
open Atom

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

val pp_foformula :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b list -> unit) ->
  Format.formatter -> ('a,'b) foformula -> unit

(** [foformula_vars fv_atom f] returns a list containing
  * all the variables that appear either bound (quantified) in [f],
  * or free in one of its atoms according to [fv_atom]. *)
val foformula_vars : ('a -> 'b list) -> ('a, 'b) foformula -> 'b list

(** {2 Meta-logic formulas} *)

type formula = (generic_atom, Vars.evar) foformula

val pp_formula : Format.formatter -> formula -> unit

(** Returns a list containing all variables that appear either bound
  * (quantified) or free in the formula. *)
val formula_vars : formula -> Vars.evar list

(** Returns a list containing all the variables that are
  * quantified inside a formula. *)
val formula_qvars : formula -> Vars.evar list

(** Substitution in a formula.
    Pre-condition: [formula subst f] require that [subst]
    co-domain does not contain any variable that is bound in [f]. *)
val subst_formula : Term.subst -> formula -> formula

(** [fresh_quantifications env f] returns a formula that is alpha-equivalent
  * to [f] but where quantified variables are fresh wrt the original
  * [!env], and it updates [env] with the declaration of these new
  * variables. *)

val fresh_quantifications : Vars.env ref -> formula -> formula

exception Not_a_disjunction

val disjunction_to_atom_list : formula -> generic_atom list
