(** Terms for the Meta-BC logic.
  *
  * This module describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(** {2 Symbols}
  *
  * We have function, name and macro symbols. Each symbol
  * can then be indexed. *)

(** Type of indexed symbols in some namespace. *)
type 'a indexed_symbol = 'a * Vars.index list

(** Names represent random values of length the security parameter. *)

type name = Symbols.name Symbols.t
type nsymb = name indexed_symbol

(** Function symbols, may represent primitives or abstract functions. *)

type fname = Symbols.fname Symbols.t
type fsymb = Symbols.fname Symbols.t * Vars.index list

(** Macros are used to represent inputs, outputs, contents of state
  * variables, and let definitions: everything that is expanded when
  * translating the meta-logic to the base logic. *)

type mname = Symbols.macro Symbols.t
type 'a msymb = mname * 'a Sorts.sort * Vars.index list

type state = Sorts.message msymb

(** {3 Pretty printing} *)

val pp_name  : Format.formatter -> name -> unit
val pp_nsymb : Format.formatter -> nsymb -> unit

val pp_fname : Format.formatter -> fname -> unit
val pp_fsymb : Format.formatter -> fsymb -> unit

val pp_mname :  Format.formatter -> mname -> unit
val pp_msymb :  Format.formatter -> 'a msymb -> unit

(** {2 Terms} *)

(** ['a term] is the type of terms of sort ['a].
  * Since index terms and just variables, and booleans are a subtype
  * of message, we are only interested in sorts [timestamp] and
  * [message]. *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

type ('a,'b) _atom = 'a * 'b * 'b

type generic_atom = [
  | `Message of (ord_eq,Sorts.message term) _atom
  | `Timestamp of (ord,Sorts.timestamp term) _atom
  | `Index of (ord_eq,Vars.index) _atom
  | `Happens of Sorts.timestamp term
]
and _ term =
  | Fun    : fsymb *  Sorts.message term list -> Sorts.message term
  | Name   : nsymb -> Sorts.message term

  | Macro  :
      'a msymb * Sorts.message term list * Sorts.timestamp term
      -> 'a term

  | Seq    : Vars.index list * Sorts.message term -> Sorts.message term
  | Pred   : Sorts.timestamp term -> Sorts.timestamp term
  | Action : Symbols.action Symbols.t * Vars.index list -> Sorts.timestamp term
  | Var    : 'a Vars.var -> 'a term

  | Diff : 'a term * 'a term -> 'a term

  | ITE :
      Sorts.boolean term * Sorts.message term * Sorts.message term ->
      Sorts.message term
  | Find :
      Vars.index list * Sorts.boolean term *
      Sorts.message term * Sorts.message term ->
      Sorts.message term

  | Atom : generic_atom -> Sorts.boolean term

  | ForAll : Vars.evar list * Sorts.boolean term -> Sorts.boolean term
  | Exists : Vars.evar list * Sorts.boolean term -> Sorts.boolean term
  | And    : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | Or     : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | Not    : Sorts.boolean term  -> Sorts.boolean term
  | Impl   : Sorts.boolean term * Sorts.boolean term -> Sorts.boolean term
  | True   : Sorts.boolean term
  | False  : Sorts.boolean term

type 'a t = 'a term

type message = Sorts.message term
type timestamp = Sorts.timestamp term
type formula = Sorts.boolean term

type message_atom = [ `Message of ord_eq * message * message ]
type trace_atom = [
  | `Timestamp of (ord,timestamp) _atom
  | `Index of (ord_eq,Vars.index) _atom
]

exception Not_a_disjunction

val disjunction_to_atom_list : formula -> generic_atom list


val pp : Format.formatter -> 'a term -> unit

val sort : 'a term -> 'a Sorts.t

exception Uncastable

(** [cast kind t] returns [t] if it is of the given sort.
  * It is used to cast terms that have been unwrapped (e.g. from
  * a substitution) to the correct type.
  * @raise Uncastable if the term does not have the expected sort. *)
val cast : 'a Sorts.sort -> 'b term -> 'a term

(** [get_vars t] returns the free variables of [t].
  * The returned list is guaranteed to have no duplicate elements. *)
val get_vars : 'a term -> Vars.evar list

(** [precise_ts t] returns a list [l] of timestamps such that
  * any term that appears in [(t)^I] that is not an attacker
  * symbol or a frame must appear in a macro applied to a timestamp
  * that is less than [sigma_T(ts)] for some [ts] in [l].
  * Concretely, this is achieved by taking the timestamps occurring
  * in [t] but only the predecessors of timestamps occurring as
  * input timestamps. *)
val precise_ts : Sorts.message term -> Sorts.timestamp term list

(** {2 Substitutions} *)

(** Substitutions for all purpose, applicable to terms and timestamps.
  * TODO unusually, we map terms to terms and not just variables to terms;
  * this is used somewhere... but I forgot where *)
type esubst = ESubst : 'a term * 'a term -> esubst

type subst = esubst list

val pp_subst : Format.formatter -> subst -> unit

(** [subst s t] applies the given substitution to [t]. *)
val subst : subst -> 'a term -> 'a term

(** [subst_var s v] returns [v'] if substitution [s] maps [v] to [Var v'],
  * and [v] if the variable is not in the domain of the substitution.
  * @raise Substitution_error if [v] is mapped to a non-variable term in [s]. *)
val subst_var : subst -> 'a Vars.var -> 'a Vars.var

(** [subst_macros_ts table l ts t] replaces [ts] by [pred(ts)] in the term [t]
  * if [ts] is applied to a state macro whose name is NOT in [l]. *)
val subst_macros_ts : 
  Symbols.table -> 
  string list -> Sorts.timestamp term -> 'a term -> 'a term

(** {2 Predefined symbols} *)

val empty : Sorts.message term

val in_macro    : Sorts.message msymb
val out_macro   : Sorts.message msymb
val frame_macro : Sorts.message msymb
val cond_macro  : Sorts.boolean msymb
val exec_macro  : Sorts.boolean msymb

val f_true   : fsymb
val f_false  : fsymb
val f_and    : fsymb
val f_or     : fsymb
val f_not    : fsymb
val f_ite    : fsymb

val f_diff   : fsymb

val f_succ   : fsymb

val f_fail   : fsymb

val f_xor    : fsymb
val f_zero   : fsymb

val f_pair   : fsymb
val f_fst    : fsymb
val f_snd    : fsymb

val f_exp    : fsymb
val f_g      : fsymb

val f_len    : fsymb
val f_zeroes : fsymb

val mk_not    : formula                 -> formula
val mk_and    : formula -> formula      -> formula
val mk_ands   : formula list            -> formula
val mk_or     : formula -> formula      -> formula
val mk_ors    : formula list            -> formula
val mk_impl   : formula -> formula      -> formula
val mk_impls  : formula list -> formula -> formula
  
val mk_forall : Vars.evar list -> formula -> formula
val mk_exists : Vars.evar list -> formula -> formula

val mk_ite    : formula -> message -> message -> message
  
val message_of_formula : formula -> message

val mk_timestamp_leq : timestamp -> timestamp -> generic_atom

val mk_indices_neq : Vars.index list -> Vars.index list -> formula
val mk_indices_eq  : Vars.index list -> Vars.index list -> formula

(** Convert a boolean term to a message term, used in frame macro definition **)
val boolToMessage : formula -> message

(** Convert from bi-terms to terms
  *
  * TODO Could we use a strong typing of [term] to make a static
  * distinction between biterms (general terms) and terms (terms
  * without diff operators)? *)

type projection = PLeft | PRight | PNone

(** Evaluate all diff operators wrt a projection.
  * If the projection is [None], the input term is returned unchanged.
  * Otherwise all diff operators are evaluated to the given
  * side and the returned term does not feature diff operators.
  * If the bi-term contains macros, and come from a bi-system, its
  * projection is only correctly interpreted if it is used inside
  * the projected system.
  * *)
val pi_term :  projection:projection -> 'a term -> 'a term

(** Evaluate topmost diff operators
  * for a given projection of a biterm.
  * For example [head_pi_term Left (diff(f(diff(a,b)),c))]
  * would be [f(diff(a,b))].
  * Macros are returned without suspended projections over them. *)
val head_pi_term : projection -> 'a term -> 'a term

(** Push topmost diff-operators just enough to expose the common
  * topmost constructor of the two projections of a biterm.
  *
  * Macros with different timestamps do not count as a common
  * constructor: [head_normal_biterm (Diff(Macro(m,l,ts),Macro(m,l,ts')))]
  * will be [Diff(Macro(m,l,ts),Macro(m,l,ts'))] and not
  * [Macro(m,l,Diff(ts,ts'))].
  *
  * If the returned biterm starts with a diff, then its immediate
  * subterms have topmost different constructors, and they do not
  * start with diffs themselves. *)
val head_normal_biterm : 'a term -> 'a term

val make_bi_term : 'a term -> 'a term -> 'a term
