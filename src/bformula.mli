(** Implements boolean formulas, both for terms and timestamps *)
open Term

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

(** {2 Atomic Formulas} *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type 'a _atom = ord * 'a * 'a

(** {2 Term formulas} *)

(** Atoms based on terms *)
type term_atom = term _atom

val term_atoms_ts : term_atom list -> timestamp list

val term_atom_vars : term_atom -> Vars.var list

val pp_term_atom : Format.formatter -> term_atom -> unit

val subst_term_atom : subst -> term_atom -> term_atom

(** Facts are boolean formulas over terms. *)

type fact = term_atom bformula

val pp_fact : Format.formatter -> fact -> unit

(** [fact_ts c] returns the timestamps appearing in [c] *)
val fact_ts : fact -> timestamp list

val subst_fact : subst -> fact -> fact

(** Negate the atom *)
val not_xpred : term_atom -> term_atom

(** Replace some subformula by the result of their evaluation
  * when it is constant. *)
val triv_eval : 'a bformula -> 'a bformula

(** Transform a formula to an equivalent one using only
  * [And] and [Or] (thus eliminating [Not] and [Impl]). *)
val simpl_fact : fact -> fact

(** Replace an atom by an equivalent list of atoms using only
  * [Eq], [Neq] and [Leq]. *)
val norm_xatom : 'a _atom -> 'a _atom list

val add_xeq :
  ord -> 'a ->
  'a list * 'a list * 'a list ->
  'a list * 'a list * 'a list

val pp_ord : Format.formatter -> ord -> unit

(** {2 Constraint formulas} *)

(** Atomic constraints are comparisons over timestamps or indices.
    Indices may only be compared for (dis)equality:
    in [Pind (o,i,i')], [o] must be either [Eq] or [Neq]. *)
type constr_atom =
  | Pts of timestamp _atom
  | Pind of Action.index _atom

val constr_atom_vars : constr_atom -> Vars.var list

(** Constr are boolean formulas over timestamps. *)

type constr = constr_atom bformula

val pp_constr_atom : Format.formatter -> constr_atom -> unit
val pp_constr : Format.formatter -> constr -> unit

(** Put a constraint in DNF using only atoms Eq, Neq and Leq *)
val constr_dnf : constr -> constr_atom list list

val subst_constr : subst -> constr -> constr

val subst_constr_atom : subst -> constr_atom -> constr_atom

(** [constr_ts c] returns the timestamps appearing in [c] *)
val constr_ts : constr -> timestamp list
