(** Terms and formulas for the Meta-BC logic.
  *
  * This modules describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** Indices are used to generate arbitrary families of terms *)
type index
type indices = index list

val pp_index : Format.formatter -> index -> unit
val pp_indices : Format.formatter -> indices -> unit

val fresh_index : unit -> index

(** Finite set of action identifiers *)
type action

val mk_action : string -> action

val pp_action : Format.formatter -> action -> unit

(** Timestamps represent positions in a trace *)

type tvar
type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action * indices

val pp_tvar : Format.formatter -> tvar -> unit
val pp_timestamp : Format.formatter -> timestamp -> unit

val fresh_tvar : unit -> tvar

(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name

type nsymb = name * indices

val pp_nsymb : Format.formatter -> nsymb -> unit

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor, xor ...
  * Adrien: already added some of them
  *)

type fname

type fsymb = fname * indices

val pp_fsymb : Format.formatter -> fsymb -> unit

(** Makes a simple function name, with no indices.
    TODO: nothing is checked here (e.g. name clashes etc).*)
val mk_fname : string -> fsymb

(** Boolean function symbols *)
val f_false : fsymb
val f_true : fsymb
val f_and : fsymb
val f_or : fsymb

(** IfThenElse function symbol *)
val f_ite : fsymb

(** Xor function symbol *)
val f_xor : fsymb

(** Successor function symbol *)
val f_succ : fsymb


(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *
  * TODO simplify design to merge name, function and state names ?
  *)

type sname

type state = sname * indices

val pp_state : Format.formatter -> state -> unit

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | State of state * timestamp
  | Output of timestamp
  | Input of timestamp

type t = term

(** Boolean formulas *)
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

(** Predicates *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt
type predicate = ord * term * term

type fact = predicate bformula

val pp_ord : Format.formatter -> ord -> unit

(** Constraints:
    - [Pind (o,i,i')] : [o] must be either [Eq] or [Neq] *)
type tpredicate =
  | Pts of ord * timestamp * timestamp
  | Pind of ord * index * index

type constr = tpredicate bformula

val pp_tpredicate : Format.formatter -> tpredicate -> unit
val pp_constr : Format.formatter -> constr -> unit

(** Put a constraint in DNF using only predicates Eq, Neq and Leq *)
val constr_dnf : constr -> tpredicate list list

(** Correspondence formulas *)


(** A formula is always of the form
  *   forall [uvars,uindices] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars,eindices] such that [econstr] and [efact]. *)
type formula = {
  uvars : tvar list;
  uindices : indices;
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : tvar list;
  eindices : indices;
  econstr : constr;
  efact : fact
}
