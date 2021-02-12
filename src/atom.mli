(** {2 Atomic Formulas} *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

(** {2 Term formulas} *)

(** Atoms based on messages *)
type message_atom = Term.message_atom

(** Atomic constraints are comparisons over timestamps or indices.
    Indices may only be compared for (dis)equality:
    in [Pind (o,i,i')], [o] must be either [Eq] or [Neq]. *)
type trace_atom = Term.trace_atom

(** Atoms of the meta-logic are either timestamp or term atoms. *)
type generic_atom = Term.generic_atom

(** Negates the atoms *)
val not_message_atom : message_atom -> message_atom
val not_trace_atom : trace_atom -> trace_atom

val tatsts :
  Term.timestamp list -> trace_atom list -> Term.timestamp list

val pp_message_atom : Format.formatter -> message_atom -> unit

val subst_message_atom : Term.subst -> message_atom -> message_atom

(** Replace an atom by an equivalent list of atoms using only
  * [Eq], [Neq] and [Leq]. *)
val norm_xatom : (ord*'a*'a) -> (ord*'a*'a) list

val add_xeq :
  ord -> 'a ->
  'a list * 'a list * 'a list ->
  'a list * 'a list * 'a list

val pp_ord : Format.formatter -> ord -> unit

val trace_atoms_ts : trace_atom list -> Term.timestamp list

val trace_atoms_ind : trace_atom list -> Vars.index list

val pp_trace_atom : Format.formatter -> trace_atom -> unit

val subst_trace_atom :
  Term.subst -> trace_atom -> trace_atom

val pp_generic_atom : Format.formatter -> generic_atom -> unit

val subst_generic_atom : Term.subst -> generic_atom -> generic_atom

val not_xpred : (ord*'a*'a) -> (ord*'a*'a)

val not_xpred_eq : (ord_eq*'a*'a) -> (ord_eq*'a*'a)
