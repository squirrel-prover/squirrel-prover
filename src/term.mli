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

(** {2 Symbols}
  *
  * We have function, name, state and macro symbols. Each symbol
  * can then be indexed.
  *
  * Names represent random values, uniformly sampled by the process.
  * State symbols reprenset memory cells.
  * Macros represent input, outputs, and let definitions:
  * everything that is expansed when translating the meta-logic to
  * the base logic.
  * TODO merge states into macros *)

(** Type of indexed symbols in some namespace *)
type 'a indexed_symbol = 'a Symbols.t * index list

(** Names are indexed and correspond to uniformly sampled nonces.
  * They are always of type message. *)
module Name : Symbols.Namespace with type data = int

type name = Name.ns Symbols.t
type nsymb = Name.ns indexed_symbol

type kind = Vars.sort

type function_symbol_info =
  | Hash_symbol
  | AEnc_symbol
  | Abstract_symbol of kind list * kind

module Function : Symbols.Namespace
  with type data = int * function_symbol_info

type fname = Function.ns Symbols.t
type fsymb = Function.ns indexed_symbol

(** The type of macro definitions, parameterized by the type of terms,
  * undefined at this point. *)
type 'a macro_info =
  | Input | Output
  | State of int * kind
    (** Macro that expands to the content of a state at a given
      * timestamp. *)
  | Global of Vars.var list * Action.index list * Vars.var * 'a
    (** [Global (inputs,indices,ts,term)] is a macro m such that
      * m(i1,..,iN)@a expands to [term] where [indices] are replaced
      * by [[i1;..;iN]], [ts] is replaced by a, and [inputs] are
      * replaced by the input macros corresponding to prefixes of a. *)
  | Local of (Vars.var*kind) list * kind * Vars.var * 'a
    (** [Simple ([x1,k1;...;xn,kn],k,ts,t)] corresponds to a macro [t]
      * with arguments [xi] of respective types [ki], and
      * return type [k].
      * Even though the macro is local it defines a global term
      * which uses a timestamp variable, given as the last Vars.var. *)

(** Type of terms, parameterized by the type of the macro namespace *)
type 'a _term =
    | Fun of Function.ns indexed_symbol * 'a _term list
    | Name of Name.ns indexed_symbol
    | MVar of var
    | Macro of 'a indexed_symbol * 'a _term list * timestamp

module rec Macro : sig
  
  include Symbols.Namespace with type data = M.t macro_info

  (** Declare a global (timestamp-dependent) macro,
    * given a term abstracted over input variables, indices,
    * and some timestamp.
    * A fresh name is generated for the macro if needed. *)
  val declare_global :
    string ->
    inputs:Vars.var list ->
    indices:Action.index list ->
    ts:Vars.var ->
    M.t -> ns Symbols.t

  (** Return the term corresponding to the declared macro,
    * if the macro can be expanded. *)
  val get_definition : ns Symbols.t -> index list -> timestamp -> M.t

  (** TODO *)
  val get_dummy_definition : ns Symbols.t -> index list -> M.t

  (** Tells whether a macro symbol can be expanded when applied
    * at a particular timestamp. *)
  val is_defined : ns Symbols.t -> timestamp -> bool

end

and M : sig type t = Macro.ns _term end

type term = Macro.ns _term

type mname = Macro.ns Symbols.t
type msymb = Macro.ns indexed_symbol

type state = msymb

(** Pretty printing *)

val pp_name : Format.formatter -> name -> unit
val pp_nsymb : Format.formatter -> nsymb -> unit

val pp_fname : Format.formatter -> fname -> unit
val pp_fsymb : Format.formatter -> fsymb -> unit

val pp_mname :  Format.formatter -> mname -> unit
val pp_msymb :  Format.formatter -> msymb -> unit

(** {2 Terms} *)

(** [term_vars t] returns the variables of [t]*)
val term_vars : term -> var list

(** [term_ts t] returns the timestamps appearing in [t] *)
val term_ts : term -> timestamp list

val pp_term : Format.formatter -> term -> unit

(** {2 Substitutions} *)

(** Substitutions for all purpose, applicable to terms and timestamps.
  * Substitutions are performed bottom to top to avoid loops. *)

type asubst =
  | Term of term * term
  | TS of timestamp * timestamp
  | Index of index * index

type subst = asubst list

val to_isubst : subst ->  (var * var) list

(** From the type of the varibles, creates the corresponding substitution. *)
val from_varsubst : (var * var) list -> subst

val pp_subst : Format.formatter -> subst -> unit

val get_index_subst : subst -> index -> index

val subst_index : subst -> index -> index
val subst_ts : subst -> timestamp -> timestamp
val subst_action : subst -> action -> action
val subst_macro : subst -> msymb -> msymb
val subst_term : subst -> term -> term

(** {2 Predefined symbols} *)

val dummy : term

val in_macro : msymb
val out_macro : msymb

val f_true : fsymb
val f_false : fsymb
val f_and : fsymb
val f_or : fsymb
val f_not : fsymb
val f_ite : fsymb

val f_pred : fsymb
val f_succ : fsymb

val f_xor : fsymb
val f_zero : fsymb

val f_pair : fsymb
val f_fst : fsymb
val f_snd : fsymb
