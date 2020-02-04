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

(** {2 Meta-logic formulas} *)

type formula = (generic_atom, Vars.evar) foformula

val pp_formula : Format.formatter -> formula -> unit

(** Substitution in a formula.
    Pre-condition: [formula subst f] require that [subst]
    co-domain does not contain any variable that is bound in [f]. *)
val subst_formula : Term.subst -> formula -> formula

exception Not_a_disjunction

val disjunction_to_atom_list : formula -> generic_atom list
