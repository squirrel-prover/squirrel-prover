open Action
(** Terms and formulas for the Meta-BC logic.
  *
  * This modules describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** Timestamps represent positions in a trace *)

type tvar
type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action

val pp_tvar : Format.formatter -> tvar -> unit
val pp_timestamp : Format.formatter -> timestamp -> unit

val fresh_tvar : unit -> tvar

(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name
val mk_name : string -> name (* TODO *)

type nsymb = name * indices

val pp_nsymb : Format.formatter -> nsymb -> unit

(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  * TODO must include builtins such as if-then-else, equality, successor, xor ...
  * Adrien: already added some of them
  *)

type fname = private Fname of string

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

(** Zero function symbol. Satisfies 0 + a -> a *)
val f_zero : fsymb

(** Successor function symbol *)
val f_succ : fsymb


(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *
  * TODO simplify design to merge name, function and state names ?
  *)

type sname
type state = sname * indices

val mk_sname : string -> sname (* TODO *)

val pp_state : Format.formatter -> state -> unit

(** Terms *)
type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | State of state * timestamp
  | Output of timestamp
  | Input of timestamp

type t = term

val pp_term : Format.formatter -> term -> unit

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

(** Atomic Formulas *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type 'a _atom = ord * 'a * 'a

type atom = term _atom

type fact = atom bformula

val pp_fact : Format.formatter -> fact -> unit

(** Negate the atom *)
val not_xpred : atom -> atom

(** Uses only And and Or (no Not, no Impl). *)
val simpl_fact : fact -> fact

(** Replace an atom by an equivalent list of atoms using only Eq,Neq and Leq *)
val norm_xatom : 'a _atom -> 'a _atom list

val add_xeq : ord -> 'a -> 'a list * 'a list * 'a list -> 'a list * 'a list * 'a list

val pp_ord : Format.formatter -> ord -> unit

(** Constraints:
    - [Pind (o,i,i')] : [o] must be either [Eq] or [Neq] *)
type tatom =
  | Pts of timestamp _atom
  | Pind of index _atom

type constr = tatom bformula

val pp_tatom : Format.formatter -> tatom -> unit
val pp_constr : Format.formatter -> constr -> unit

(** Put a constraint in DNF using only atoms Eq, Neq and Leq *)
val constr_dnf : constr -> tatom list list


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

val ivar_subst_state : index subst -> state -> state

val tvar_subst_term : tvar subst -> term -> term
val ivar_subst_term : index subst -> term -> term
val subst_term : index subst -> tvar subst -> term -> term

val tvar_subst_fact : tvar subst -> fact -> fact
val ivar_subst_fact : index subst -> fact -> fact
val subst_fact : index subst -> tvar subst -> fact -> fact

val tvar_subst_constr : tvar subst -> constr -> constr
val ivar_subst_constr : index subst -> constr -> constr
val subst_constr : index subst -> tvar subst -> constr -> constr


(** Timestamp variables substitution in a post-condition.
    Pre-condition: [tvar_subst_postcond subst pc] require that [subst]
    co-domain is fresh in [pc]. *)
val tvar_subst_postcond : tvar subst -> postcond -> postcond

  (** Index variables substitution in a post-condition.
    Pre-condition: [ivar_subst_postcond isubst pc] require that [isubst]
    co-domain is fresh in [pc]. *)
val ivar_subst_postcond : index subst -> postcond -> postcond

(** Substitution in a post-condition.
    Pre-condition: [subst_postcond isubst tsubst pc] require that [isubst]
    and [tsubst] co-domains are fresh in [pc]. *)
val subst_postcond : index subst -> tvar subst -> postcond -> postcond



(** [term_vars t] returns the timestamp and index variables of [t]*)
val term_vars : term -> tvar list * index list

(** [tss_vars tss] returns the timestamp and index variables of [tss]*)
val tss_vars : timestamp list -> tvar list * index list


(** [term_ts t] returns the timestamps appearing in [t] *)
val term_ts : term -> timestamp list
