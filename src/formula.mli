(** Implements first order formulas, with atoms both on terms and timestamps *)
open Atom

(** {2 Generic first-order formulas} *)

exception Not_a_disjunction

val disjunction_to_atom_list : Term.formula -> generic_atom list
