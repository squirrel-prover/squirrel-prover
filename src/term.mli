open Vars
open Action
(** Terms for the Meta-BC logic.
  *
  * This module describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** {2 Timestamps} *)
(** Timestamps represent positions in a trace *)
type timestamp =
  | TVar of var
  | TPred of timestamp
  | TName of action

val pp_timestamp : Format.formatter -> timestamp -> unit

val action_of_ts : timestamp -> Action.action option

val ts_vars : timestamp -> Vars.var list

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
  | MVar of var
  | State of state * timestamp
  | Macro of msymb * timestamp

type t = term

(** [term_vars t] returns the variables of [t]*)
val term_vars : term -> var list

(** [term_ts t] returns the timestamps appearing in [t] *)
val term_ts : term -> timestamp list

val dummy : term

val pp_term : Format.formatter -> term -> unit

(** [is_built_in mn] returns true iff [mn] is a built-in.  *)
val is_built_in : mname -> bool

(** Converts a string to a macro name if a macro of that name exists,
  * raises [Not_found] otherwise. *)
val is_declared : string -> mname

(** Reset macro declarations *)
val initialize_macros : unit -> unit

(** [declare_macro x l f] declares a new macro with a name resembling [x],
  * where [f] is used to compute how the macro is expanded, and expansion
  * is only allowed for explicit actions of length [l].
  *
  * TODO [f] should actually do only basic things (conversion,
  * substitutions, and computation of action prefixes to obtain correct
  * input symbols) and in fact [f] is always the same: at some point
  * it would be good to avoid this closure. *)
val declare_macro : string -> int -> (action -> index list -> term) -> mname

(** Return the term corresponding to the declared macro, except for the
    built-ins "in" and "out". *)
val macro_declaration : mname -> action -> index list -> term

(** Given the name of a defined macro, returns the action length that
  * is required for unrolling that macro. *)
val macro_domain : mname -> int

val mk_mname : mname -> index list -> msymb

val in_macro : msymb
val out_macro : msymb

(** {2 Substitutions} *)
(** Substitutions for all purpose, applicable to terms and timestamps alikes.
    Substitutions are performed bottom to top to avoid loops. *)

type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of index * index

type subst = asubst list

val to_isubst : subst ->  (var * var) list

(** From the type of the varibles, creates the corresponding substitution. *)
val from_varsubst : (var * var) list -> subst

val pp_subst : Format.formatter -> subst -> unit

val get_term_subst : subst -> term -> term
val get_ts_subst : subst -> timestamp -> timestamp
val get_index_subst : subst -> index -> index

val subst_index : subst -> index -> index
val subst_ts : subst -> timestamp -> timestamp
val subst_action : subst -> action -> action
val subst_state : subst -> state -> state
val subst_term : subst -> term -> term
