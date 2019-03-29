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

(** Finite set of action identifiers *)
type action

val pp_action : Format.formatter -> action -> unit

(** Timestamps represent positions in a trace *)

type tvar
type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action * indices

val pp_tvar : Format.formatter -> tvar -> unit
val pp_timestamp : Format.formatter -> timestamp -> unit

(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name

type nsymb = name * indices

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor...
  *)

type fname

type fsymb = fname * indices

(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *
  * TODO simplify design to merge name, function and state names ?
  *)

type sname

type state = sname * indices

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | State of state * timestamp
  | Output of timestamp
  | Input of timestamp

(** Boolean formulas *)
type 'a bformula =
  | And of 'a bformula * 'a bformula
  | Or of 'a bformula * 'a bformula
  | Not of 'a bformula
  | Impl of 'a bformula * 'a bformula
  | Atom of 'a

val pp_bformula :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a bformula -> unit

(** Predicates *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt
type predicate = ord * term * term

type fact = predicate bformula

val pp_ord : Format.formatter -> ord -> unit

(** Constraints *)

type tpredicate = ord * timestamp * timestamp
type constr = tpredicate bformula

val pp_tpredicate : Format.formatter -> tpredicate -> unit
val pp_constr : Format.formatter -> constr -> unit

(** Correspondence formulas *)


(** A formula is always of the form
  *   forall [uvars] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars] such that [econstr] and [efact]. *)
type formula = {
  uvars : tvar list;
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : tvar list;
  econstr : constr;
  efact : fact
}
