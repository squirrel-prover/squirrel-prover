(** {2 Atomic Formulas} *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

(** {2 Term formulas} *)

(** Atoms based on terms *)
type term_atom = [ `Message of ord_eq * Term.term * Term.term ]

(** Atomic constraints are comparisons over timestamps or indices.
    Indices may only be compared for (dis)equality:
    in [Pind (o,i,i')], [o] must be either [Eq] or [Neq]. *)
type trace_formula_atom = [
  | `Timestamp of ord * Term.timestamp * Term.timestamp
  | `Index of ord_eq * Index.t * Index.t
]

(** Atoms of the meta-logic are either timestamp or term atoms. *)
type generic_atom = [
  | term_atom
  | trace_formula_atom
  | `Happens of Term.timestamp
]

val atsts : Term.timestamp list -> term_atom list -> Term.timestamp list
val tatsts :
  Term.timestamp list -> trace_formula_atom list -> Term.timestamp list

val term_atoms_ts : term_atom list -> Term.timestamp list

val term_atom_vars : term_atom -> Vars.var list

val pp_term_atom : Format.formatter -> term_atom -> unit

val subst_term_atom : Term.subst -> term_atom -> term_atom

(** Replace an atom by an equivalent list of atoms using only
  * [Eq], [Neq] and [Leq]. *)
val norm_xatom : (ord*'a*'a) -> (ord*'a*'a) list

val add_xeq :
  ord -> 'a ->
  'a list * 'a list * 'a list ->
  'a list * 'a list * 'a list

val add_xeq_eq :
  ord_eq -> 'a ->
  'a list * 'a list ->
  'a list * 'a list

val pp_ord : Format.formatter -> ord -> unit

val trace_formula_atom_vars : trace_formula_atom -> Vars.var list

val pp_trace_formula_atom : Format.formatter -> trace_formula_atom -> unit

val subst_trace_formula_atom :
  Term.subst -> trace_formula_atom -> trace_formula_atom

val generic_atom_var : generic_atom -> Vars.var list

val pp_generic_atom : Format.formatter -> generic_atom -> unit

val subst_generic_atom : Term.subst -> generic_atom -> generic_atom

val not_xpred : (ord*'a*'a) -> (ord*'a*'a)

val not_xpred_eq : (ord_eq*'a*'a) -> (ord_eq*'a*'a)
