(** Terms for the Meta-BC logic.
  *
  * This module describes the syntax of the logic. It does not
  * provide low-level representations, normal forms, etc. that
  * are to be used in automated reasoning, nor does it provide
  * representations necessary for the front-end involving
  * processes, axioms, etc. *)

(*------------------------------------------------------------------*)
(** {2 Symbols}
  *
  * We have function, name and macro symbols. Each symbol
  * can then be indexed. *)

(** Ocaml type of a typed index symbol.
    Invariant: [s_typ] do not contain tvar or univars *)
type ('a,'b) isymb = private { 
  s_symb    : 'a;
  s_indices : Vars.index list;
  s_typ     : 'b; 
}

val mk_isymb : 'a -> Type.tmessage -> Vars.index list -> ('a,Type.tmessage) isymb

(** Names represent random values of length the security parameter. *)

type name = Symbols.name Symbols.t
type nsymb = (name, Type.tmessage) isymb

(** Function symbols, may represent primitives or abstract functions. *)

type fname = Symbols.fname Symbols.t
type fsymb = fname * Vars.index list

(** Macros are used to represent inputs, outputs, contents of state
  * variables, and let definitions: everything that is expanded when
  * translating the meta-logic to the base logic. *)

type mname    = Symbols.macro Symbols.t
type msymb = (mname, Type.tmessage) isymb

type state = msymb

(*------------------------------------------------------------------*)
(** {3 Pretty printing} *)

val pp_name  : Format.formatter -> name -> unit
val pp_nsymb : Format.formatter -> nsymb -> unit

val pp_fname : Format.formatter -> fname -> unit
val pp_fsymb : Format.formatter -> fsymb -> unit

val pp_mname :  Format.formatter -> mname -> unit
val pp_msymb :  Format.formatter -> msymb -> unit

(*------------------------------------------------------------------*)
(** {2 Terms} *)

(** ['a term] is the type of terms of sort ['a].
  * Since index terms and just variables, and booleans are a subtype
  * of message, we are only interested in sorts [timestamp] and
  * [message]. *)

type ord = [ `Eq | `Neq | `Leq | `Geq | `Lt | `Gt ]
type ord_eq = [ `Eq | `Neq ]

val pp_ord   : Format.formatter -> ord -> unit
  
type ('a,'b) _atom = 'a * 'b * 'b

type generic_atom = [
  | `Message of (ord_eq,Type.message term) _atom
  | `Timestamp of (ord,Type.timestamp term) _atom
  | `Index of (ord_eq,Vars.index) _atom
  | `Happens of Type.timestamp term
]
and _ term =
  | Fun    : fsymb * Type.ftype * Type.message term list -> Type.message term
  | Name   : nsymb -> Type.message term

  | Macro  :
      msymb * Type.message term list * Type.timestamp term
      -> Type.message term

  | Seq    : Vars.index list * Type.message term -> Type.message term
  | Pred   : Type.timestamp term -> Type.timestamp term
  | Action : Symbols.action Symbols.t * Vars.index list -> Type.timestamp term
  | Var    : 'a Vars.var -> 'a term

  | Diff : 'a term * 'a term -> 'a term

  | Find :
      Vars.index list * Type.message term *
      Type.message term * Type.message term ->
      Type.message term

  | Atom : generic_atom -> Type.message term

  | ForAll : Vars.evar list * Type.message term -> Type.message term
  | Exists : Vars.evar list * Type.message term -> Type.message term

type 'a t = 'a term

type message = Type.message term
type timestamp = Type.timestamp term

type eterm = ETerm : 'a term -> eterm

(** Does not recurse. *)
val tmap  : (eterm -> eterm) -> 'a term -> 'a term 
val titer : (eterm -> unit) -> 'a term -> unit
val tfold : (eterm -> 'a -> 'a) -> 'b term -> 'a -> 'a

(*------------------------------------------------------------------*)
(** {2 Subset of all atoms} *)
(** (the subsets are not disjoint). *)

type message_atom = [ `Message of (ord_eq,Type.message term) _atom]

type index_atom = [ `Index of (ord_eq,Vars.index) _atom]
                    
type trace_atom = [
  | `Timestamp of (ord,timestamp) _atom
  | `Index     of (ord_eq,Vars.index) _atom
  | `Happens   of Type.timestamp term
]

type trace_eq_atom = [
  | `Timestamp of (ord_eq,timestamp)  _atom
  | `Index     of (ord_eq,Vars.index) _atom
]

type eq_atom = [
  | `Message   of (ord_eq, message) _atom
  | `Timestamp of (ord_eq, timestamp) _atom
  | `Index     of (ord_eq, Vars.index) _atom
]

val pp_eq_atom    : Format.formatter -> eq_atom    -> unit
val pp_trace_atom : Format.formatter -> trace_atom -> unit

(*------------------------------------------------------------------*)
(** Literals. *)

type literal = [`Neg | `Pos] * generic_atom

type eq_literal = [`Pos | `Neg] * eq_atom

type trace_literal = [`Pos | `Neg] * trace_atom

val pp_literal  : Format.formatter -> literal      -> unit
val pp_literals : Format.formatter -> literal list -> unit

val pp_trace_literal  : Format.formatter -> trace_literal      -> unit
val pp_trace_literals : Format.formatter -> trace_literal list -> unit

val neg_lit : literal -> literal 

val neg_trace_lit : trace_literal -> trace_literal 

val disjunction_to_literals : message -> literal list option

(*------------------------------------------------------------------*)
(** {2 Pretty-printer and cast} *)

val pp : Format.formatter -> 'a term -> unit

val kind : 'a term -> 'a Type.kind
    
val ty  : ?ty_env:Type.Infer.env -> 'a term -> 'a Type.ty
val ety : ?ty_env:Type.Infer.env -> 'a term -> Type.ety

(*------------------------------------------------------------------*)
exception Uncastable

(** [cast k t] checks that [t] can be seen as a message of kind [k].
    @raise Uncastable if the term cannot be cast.*)
val cast : 'a Type.kind -> 'b term -> 'a term

(*------------------------------------------------------------------*)
(** [get_vars t] returns the free variables of [t].
  * The returned list is guaranteed to have no duplicate elements. *)
val get_vars : 'a term -> Vars.evar list

(** [fv t] returns the free variables of [t]. *)
val fv : 'a term -> Vars.Sv.t

val f_triv : message -> bool

(** [precise_ts t] returns a list [l] of timestamps such that
  * any term that appears in [(t)^I] that is not an attacker
  * symbol or a frame must appear in a macro applied to a timestamp
  * that is less than [sigma_T(ts)] for some [ts] in [l].
  * Concretely, this is achieved by taking the timestamps occurring
  * in [t] but only the predecessors of timestamps occurring as
  * input timestamps. *)
val precise_ts : Type.message term -> Type.timestamp term list

(*------------------------------------------------------------------*)
(** {2 Substitutions} *)

(** Substitutions for all purpose, applicable to terms and timestamps.
  * TODO unusually, we map terms to terms and not just variables to terms;
  * this is used somewhere... but I forgot where *)
type esubst = ESubst : 'a term * 'a term -> esubst

type subst = esubst list

val pp_subst : Format.formatter -> subst -> unit

(** term substitution *)
val subst : subst -> 'a term -> 'a term

(** substitute type variables *)
val tsubst : Type.tsubst -> 'a term -> 'a term

(** [subst_var s v] returns [v'] if substitution [s] maps [v] to [Var v'],
  * and [v] if the variable is not in the domain of the substitution.
  * @raise Substitution_error if [v] is mapped to a non-variable term in [s]. *)
val subst_var : subst -> 'a Vars.var -> 'a Vars.var

(** Substitute indices in an indexed symbols. *)
val subst_isymb : subst -> ('a,'b) isymb -> ('a,'b) isymb

(** [subst_macros_ts table l ts t] replaces [ts] by [pred(ts)] in the term [t]
  * if [ts] is applied to a state macro whose name is NOT in [l]. *)
val subst_macros_ts : 
  Symbols.table -> 
  string list -> Type.timestamp term -> 'a term -> 'a term

(*------------------------------------------------------------------*)
(** {2 Matching and rewriting} *)

module Match : sig
  type mv

  (** A pattern is a list of free type variables, a term [t] and a subset
      of [t]'s free variables that must be matched. 
      The free type variables must be inferred. *)
  type 'a pat = { 
    pat_tyvars : Type.tvars; 
    pat_vars : Vars.Sv.t; 
    pat_term : 'a term; 
  }

  val to_subst : mv -> subst

  (** [try_match t p] tries to match [p] with [t] (at head position). 
      If it succeeds, it returns a map instantiating the variables [p.pat_vars] 
      as substerms of [t]. *)
  val try_match : 'a term -> 'b pat -> [`FreeTyv | `NoMatch | `Match of mv] 

  (** Occurrence matched *)
  type 'a match_occ = { occ : 'a term;
                        mv  : mv; }

  (** [find t pat] looks for an occurence [t'] of [pat] in [t],
      where [t'] is a subterm of [t] and [t] and [t'] are unifiable by [θ].
      It returns the occurrence matched [{occ = t'; mv = θ}]. *)
  val find : 'a term -> 'b pat -> 'b match_occ option

  (** [find_map t p func] behaves has [find], but also computes the term 
      obtained from [t] by replacing:
      - if [many = false], a *single* occurence of [pat] by [func t' θ]. 
      - if [many = true], all occurences found. *)
  val find_map :
    many:bool -> 'a term -> 'b pat -> ('b term -> mv -> 'b term) -> 
    ('b match_occ list * 'a term) option
end

(*------------------------------------------------------------------*)
(** {2 Builtins function symbols} *)

val empty : message 
val init : timestamp

val in_macro    : msymb
val out_macro   : msymb
val frame_macro : msymb
val cond_macro  : msymb
val exec_macro  : msymb

val f_true   : fsymb
val f_false  : fsymb
val f_and    : fsymb
val f_impl   : fsymb
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

val f_of_bool   : fsymb

val f_len    : fsymb
val f_zeroes : fsymb
  
(*------------------------------------------------------------------*)
(** {2 Smart constructors} *)

(*------------------------------------------------------------------*)
(** {3 For terms} *)

val mk_fun :
  Symbols.table ->
  fname ->
  Vars.index list ->
  Type.message term list ->
  Type.message term
    
val mk_true    : message
val mk_false   : message
val mk_zero    : message
val mk_fail    : message
val mk_len     : message -> message
val mk_zeroes  : message -> message
val mk_of_bool : message -> message
val mk_pair    : message -> message -> message
 
(*------------------------------------------------------------------*)
(** {3 For messages} *)

val mk_not    : ?simpl:bool -> message                 -> message
val mk_and    : ?simpl:bool -> message -> message      -> message
val mk_ands   : ?simpl:bool -> message list            -> message
val mk_or     : ?simpl:bool -> message -> message      -> message
val mk_ors    : ?simpl:bool -> message list            -> message
val mk_impl   : ?simpl:bool -> message -> message      -> message
val mk_impls  : ?simpl:bool -> message list -> message -> message
  
val mk_forall : Vars.evar list -> message -> message
val mk_exists : Vars.evar list -> message -> message

val mk_ite : ?simpl:bool -> message -> message -> message -> message
  
val mk_timestamp_leq : timestamp -> timestamp -> generic_atom

val mk_indices_neq : Vars.index list -> Vars.index list -> message
val mk_indices_eq  : Vars.index list -> Vars.index list -> message

(*------------------------------------------------------------------*)
(** {2 Simplification} *)

val not_message_atom  : message_atom  -> message_atom
val not_index_atom    : index_atom    -> index_atom
val not_trace_eq_atom : trace_eq_atom -> trace_eq_atom

val not_simpl : message -> message

(*------------------------------------------------------------------*)
(** {2 Destructors} *)

val destr_action : 
  timestamp -> (Symbols.action Symbols.t * Vars.index list) option

val destr_forall : message -> (Vars.evar list * message) option
val destr_exists : message -> (Vars.evar list * message) option

(*------------------------------------------------------------------*)
val destr_false : message ->               unit  option
val destr_true  : message ->               unit  option
val destr_not   : message ->            message  option
val destr_and   : message -> (message * message) option
val destr_or    : message -> (message * message) option
val destr_impl  : message -> (message * message) option

(*------------------------------------------------------------------*)
val is_false : message -> bool
val is_true  : message -> bool
val is_not   : message -> bool
val is_and   : message -> bool
val is_or    : message -> bool
val is_impl  : message -> bool

(*------------------------------------------------------------------*)
(** left-associative *)
val destr_ands  : int -> message -> message list option
val destr_ors   : int -> message -> message list option
val destr_impls : int -> message -> message list option

val decompose_forall : message -> Vars.evar list * message
val decompose_exists : message -> Vars.evar list * message

(*------------------------------------------------------------------*)
val decompose_ands  : message -> message list 
val decompose_ors   : message -> message list 
val decompose_impls : message -> message list 

(*------------------------------------------------------------------*)
val destr_var : 'a term -> 'a Vars.var option
val destr_pair : message -> (message * message) option

(*------------------------------------------------------------------*)
val destr_matom : generic_atom -> (ord_eq * message * message) option 

(*------------------------------------------------------------------*)
(** {2 Sets and Maps } *)

module St : Set.S with type elt = eterm
module Mt : Map.S with type key = eterm

(*------------------------------------------------------------------*)
(** {2 Convert from bi-terms to terms}
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
