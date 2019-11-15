open Vars
open Action
(** Terms and formulas for the Meta-BC logic.
  *
  * This module describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** {2 Timestamps} *)
(** Timestamps represent positions in a trace *)
module Tvar : VarType

type tvar = Tvar.t

type timestamp =
  | TVar of tvar
  | TPred of timestamp
  | TName of action

val pp_timestamp : Format.formatter -> timestamp -> unit

val action_of_ts : timestamp -> Action.action option

(** {2 Messages } *)
(** Messages variables for formulas **)
module Mvar : VarType
  
type mvar = Mvar.t


(** {2 Names} *)
(** Names represent random values, uniformly sampled by the process.
  * A name symbol is derived from a name (from a finite set) and
  * a list of indices. *)

type name

val pp_name : Format.formatter -> name -> unit

val mk_name : string -> name (* TODO *)

val string_of_name : name -> string

(** {2 Functions} *)
(** Function symbols are built from a name (from a finite set)
  * and a list of indices.
  *
  *)
type nsymb = name * index list

val pp_nsymb : Format.formatter -> nsymb -> unit


type fname = private Fname of string

val pp_fname : Format.formatter -> fname -> unit

type fsymb = fname * index list

val pp_fsymb : Format.formatter -> fsymb -> unit

(** Makes a simple function name, with no indices.
    TODO: nothing is checked here (e.g. name clashes etc).*)
val mk_fname : string -> fsymb
val mk_fname_idx : string -> index list -> fsymb

(** Boolean function symbols *)
val f_false : fsymb
val f_true : fsymb
val f_and : fsymb
val f_or : fsymb
val f_not : fsymb

(** IfThenElse function symbol *)
val f_ite : fsymb

(** Xor function symbol *)
val f_xor : fsymb

(** Zero function symbol. Satisfies 0 + a -> a *)
val f_zero : fsymb

(** Successor function symbol *)
val f_succ : fsymb


(** {2 States} *)
(** Memory cells are represented by state variable, themselves
  * derived from a name (from a finite set) and indices.
  *)

type sname
type state = sname * index list

val mk_sname : string -> sname (* TODO *)

val pp_state : Format.formatter -> state -> unit

(** Type of macros name.
    A macro is either a user-defined macro, through a let construct in
    a process, or a built-in macro such as "in" or "out". *)

type mname = private string
type msymb = mname * index list

val pp_mname :  Format.formatter -> mname -> unit
val pp_msymb :  Format.formatter -> msymb -> unit



(** {2 Terms} *)

type term =
  | Fun of fsymb * term list
  | Name of nsymb
  | MVar of mvar
  | State of state * timestamp
  | Macro of msymb * timestamp

type t = term

val dummy : term

val pp_term : Format.formatter -> term -> unit

(** [is_built_in mn] returns true iff [mn] is a built-in.  *)
val is_built_in : mname -> bool

val is_declared : string -> mname

(** Reset macro declarations *)
val initialize_macros : unit -> unit

(** [declare_macro x f] declares a new macro with a name resembling [x],
  * associated to a substitution function which takes the target timestamp
  * as argument. *)
val declare_macro : string -> (timestamp -> index list -> term) -> mname

(** Return the term corresponding to the declared macro, except for the
    built-ins "in" and "out". *)
val macro_declaration : mname -> timestamp -> index list -> term

val mk_mname : mname -> index list -> msymb

val in_macro : msymb
val out_macro : msymb


(** {2 Generic Formulas} *)
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

(** [atoms b] returns the list of atoms appearing in [b] *)
val atoms : 'a bformula -> 'a list

(** Atomic Formulas *)

type ord = Eq | Neq | Leq | Geq | Lt | Gt

type 'a _atom = ord * 'a * 'a

type atom = term _atom

val pp_atom : Format.formatter -> atom -> unit

type fact = atom bformula

val pp_fact : Format.formatter -> fact -> unit

(** Negate the atom *)
val not_xpred : atom -> atom

(** Evaluate trivial subformula. *)
val triv_eval : 'a bformula -> 'a bformula

(** Uses only And and Or (no Not, no Impl). *)
val simpl_fact : fact -> fact

(** Replace an atom by an equivalent list of atoms using only Eq,Neq and Leq *)
val norm_xatom : 'a _atom -> 'a _atom list

val add_xeq :
  ord -> 'a ->
  'a list * 'a list * 'a list ->
  'a list * 'a list * 'a list

val pp_ord : Format.formatter -> ord -> unit

(** Atomic constraints are comparisons over timestamps or indices.
    Indices may only be compared for (dis)equality, i.e.
    Constraints:
    - [Pind (o,i,i')] : [o] must be either [Eq] or [Neq] *)
type tatom =
  | Pts of timestamp _atom
  | Pind of index _atom

type constr = tatom bformula

val pp_tatom : Format.formatter -> tatom -> unit
val pp_constr : Format.formatter -> constr -> unit

(** Put a constraint in DNF using only atoms Eq, Neq and Leq *)
val constr_dnf : constr -> tatom list list


(** {2 Correspondence formulas} *)
(** Formulas depends on variables inside [fvar]. *)
type fvar =
  | TSVar of tvar
  | MessVar of mvar
  | IndexVar of index

val pp_typed_fvar : Format.formatter -> fvar -> unit

val pp_typed_fvars : string -> Format.formatter -> fvar list -> unit

val make_fresh_of_type : fvar -> fvar

(** A formula is always of the form
  *   forall [uvars,uindices] such that [uconstr],
  *   [ufact] => [postcond],
  * with a postcondition that is a disjunction
  * of formulas of the form
  *   exists [evars,eindices] such that [econstr] and [efact]. *)
type formula = {
  uvars : fvar list;
  uconstr : constr;
  ufact : fact;
  postcond : postcond list
}
and postcond = {
  evars : fvar list;
  econstr : constr;
  efact : fact
}

val get_tsvars : fvar list -> tvar list

val get_messvars : fvar list -> mvar list

val get_indexvars :fvar list -> index list


val pp_postcond : Format.formatter -> postcond -> unit
val pp_formula : Format.formatter -> formula -> unit

(** {2 Substitutions} *)
(** Substitutions for all purpose, applicable to terms and timestamps alikes.
    Substitutions are performed bottom to top to avoid loops. *)
type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of index * index

type subst = asubst list

val to_isubst : subst ->  (index * index) list

val from_tvarsubst : (tvar * tvar) list -> subst
val from_isubst : (index * index) list -> subst
val from_fvarsubst : (fvar * fvar) list -> subst

val pp_subst : Format.formatter -> subst -> unit

val subst_index : subst -> index -> index
val subst_ts : subst -> timestamp -> timestamp
val subst_action : subst -> action -> action
val subst_state : subst -> state -> state
val subst_term : subst -> term -> term
val subst_fact : subst -> fact -> fact
val subst_constr : subst -> constr -> constr

(** Substitution in a post-condition.
    Pre-condition: [subst_postcond subst pc] require that [subst]
    co-domain is fresh in [pc]. *)
val subst_postcond : subst -> postcond -> postcond

(** [fresh_postcond p] instantiates [p] with fresh variables for variables
    in p.evars *)
val fresh_postcond : postcond ->  postcond

(** [term_vars t] returns the timestamp and index variables of [t]*)
val term_vars : term -> tvar list * index list

(** [tss_vars tss] returns the timestamp and index variables of [tss]*)
val tss_vars : timestamp list -> tvar list * index list


(** [term_ts t] returns the timestamps appearing in [t] *)
val term_ts : term -> timestamp list

(** [atoms_ts ats] returns the timestamps appearing in [ats] *)
val atoms_ts : atom list -> timestamp list

(** [fact_ts f] returns the timestamps appearing in [f] *)
val fact_ts : fact -> timestamp list

(** [constr_ts c] returns the timestamps appearing in [c] *)
val constr_ts : constr -> timestamp list
