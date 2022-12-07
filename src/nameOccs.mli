module PathCond = Iter.PathCond

(*------------------------------------------------------------------*)
(** Generic functions to search illegal occurrences of names,
    and generate the appropriate proof obligations,
    For use when writing tactics, e.g. gdh or fresh. *)

open Term

(** {1 Types and functions to handle generic occurrences}

    Occurrences have associated data and conditions, source timestamps,
    etc.

    {b TODO}:
    - This should probably go in a module with a generic name,
      which would be used by this module (and others).
    - This is probably somewhat redundant with {!Iter.occ}…
      but more specific to the use case here. *)

(** Tag indicating whether an occurrence is direct,
    or indirectly caused by some action given as a {!Term.term}. *)
type occ_type =
  | EI_direct
  | EI_indirect of term

(** Applies a substitution to an {!occ_type}. *)
val subst_occtype : subst -> occ_type -> occ_type

(** Simple occurrence of an element of type ['a],
    with additional data of type ['b]. *)
type ('a, 'b) simple_occ =
  {so_cnt     : 'a;        (** content of the occurrence *)
   so_coll    : 'a;        (** thing it potentially collides with *)
   so_ad      : 'b;        (** additional data, if needed *)
   so_vars    : Vars.vars; (** variables bound above the occurrence *)
   so_cond    : terms;     (** condition above the occurrence *)
   so_occtype : occ_type;  (** occurrence type *)
   so_subterm : term;      (** a subterm where the occurrence was found (for printing) *)
  }

(** Constructs a simple occurrence. *)
val mk_simple_occ : 'a -> 'a -> 'b -> Vars.vars -> terms -> occ_type -> term -> ('a, 'b) simple_occ

(** {2 Derived occurrence types} *)

(** Type of a timestamp occurrence. *)
type ts_occ = (term, unit) simple_occ

(** Type of empty simple occurrences
    (used as dummy parameter when they are not needed). *)
type empty_occ = (unit, unit) simple_occ

type ts_occs = ts_occ list

type ('a, 'b) simple_occs = (('a, 'b) simple_occ) list

type empty_occs = empty_occ list

(** {2 Extended occurrences} *)

(** Occurrence with additional info about where it was found. *)
type ('a, 'b) ext_occ = {
  eo_occ       : ('a, 'b) simple_occ;
  eo_source    : terms;     (** Original terms where the occurrence was found. *)
  eo_source_ts : ts_occs;   (** Timestamps occurring in the source terms. *)

  eo_path_cond : Iter.PathCond.t;
  (** Path condition on the timestamps [τ] at which the occurrence can occur:
      for any source timestamp [τ_src] (in [eo_sources_ts]),
      [path_cond τ τ_src] *)
}

type ('a, 'b) ext_occs = (('a, 'b) ext_occ) list

(** {2 Occurrence formulas} *)

(** Type of a function generating a formula meant to say
    "the occurrence is actually a collision" (or its negation).

    Arguments are:
    - occurrence content,
    - what the occurrence potentially collides with,
    - the associated data.

    We also use this formula to compute occurrence subsumption
    (if o1 generates a particular case of o2 then it is subsumed;
    {b TODO} clarify this comment). *)
type ('a, 'b) occ_formula =
  negate:bool -> 'a -> 'a -> 'b -> term

(*------------------------------------------------------------------*)

(** {1 Macro expansion}
    Functions handling macro expansion in terms, when allowed. *)

(** Information used to check if a macro can be expanded in a term:
    - a tag indicating the occurrence type (and provenance);
    - the trace context. *)
type expand_info = occ_type * Constr.trace_cntxt

(** Expands a term [t] if it is a macro
    and we can check that its timestamp happens
    using [info] (not recursively).
    Returns [Some t'] if [t] expands to [t'],
    [None] if no expansion has been performed. *)
val expand_macro_check_once : expand_info -> term -> term option

(** Expands term as much as possible, recursively
    (only at toplevel, not in subterms). *)
val expand_macro_check_all : expand_info -> term -> term

(** Returns all timestamps occuring in macros in a list of terms.
    Should only be used when sources are directly occurring,
    not themselves produced by unfolding macros. *)
val get_macro_actions : Constr.trace_cntxt -> term list -> ts_occs


(*------------------------------------------------------------------*)

(** {1 Formula construction and simplification} *)

(** Interprets [phi] as [phi_1 /\ … /\ phi_n]
    and reconstructs it to simplify trivial equalities. *)
val clear_trivial_equalities : term -> term

(** Constructs the formula
    
    [(∃ v1. path_cond τ ts1 ∨ … ∨ ∃ vn. path_cond τ tsn)]

    where [vi], [tsi] are the variables and content of [ts_occ]. 
    (for example, [path_cond x y] can be [x ≤ y]). *)
val time_formula : term -> ?path_cond:PathCond.t -> ts_occs -> term


(*------------------------------------------------------------------*)

(** {1 Name occurrences} *)

module Name : sig
  (** An applied named [symb(args)] *)
  type t = { symb : Term.nsymb; args : Term.terms; }

  val pp : Format.formatter -> t -> unit

  val of_term : Term.t -> t

  val to_term : t -> Term.t

  val subst : Term.subst -> t -> t

  (** looks for a name with the same symbol in the list *)
  val exists_name : t -> t list -> bool

  (** finds all names with the same symbol in the list *)
  val find_name : t -> t list -> t list
end

type n_occ = (Name.t, unit) simple_occ
type n_occs = n_occ list

type name_occ = (Name.t, unit) ext_occ
type name_occs = name_occ list

(** Constructs a name occurrence. *)
val mk_nocc :
  Name.t ->      (* name *)
  Name.t ->      (* name it collides with *)
  Vars.vars -> (* vars bound above *)
  terms ->     (* condition above *)
  occ_type ->  (* occurrence type *)
  term ->      (* subterm (for printing) *)
  n_occ


(** Finds all names with the same symbol in the list, returns the
    corresponding n_occs *)
val find_name_occ :
  Name.t -> Name.t list ->
  Vars.vars -> Term.terms -> occ_type -> Term.term ->
  n_occs

  
(** {2 Searching for illegal name occurrences} *)

(** Type of a function that takes a term, and generates
    a list of its name occurrences.
    Also returns a list of [('a, 'b) simple_occs], used to record
    information gathered during the exploration of the term
    (the additional data field can be used to record anything,
     e.g. {b TODO}).

    Uses:
    - A continuation of type [unit -> n_occs * 'a, 'b simple_occs]
      when it does not want to handle the term it's given,
      and just asks to be called again on the subterms.
    - A continuation of type
      [fv -> cond -> p -> se -> st -> term -> n_occs * ('a,'b) simple_occs]
      that calls the function again on the given parameters,
      for when it needs to do finer things
      (typically handle some of the subterms manually,
       and call this continuation on the remaining ones,
       or handle subterms at depth 1 by hand,
       and call the continuation on subterms at depth 2).
      Functions of this type don't need to unfold macros,
      which are handled separately.

    Other parameters:
    - [info]: information to expand macros,
      including system at current position.
    - [fv]: variables bound above the current position.
    - [cond]: condition at the current position.
    - [p]: current position.
    - [st]: a surrounding subterm, for printing purposes. *)
type ('a, 'b) f_fold_occs =
  (unit -> n_occs * ('a, 'b) simple_occs) ->
  (fv:Vars.vars ->
   cond:terms ->
   p:Match.Pos.pos ->
   info:expand_info ->
   st:term ->
   term ->
   n_occs * ('a, 'b) simple_occs)->
  info:expand_info ->
  fv:Vars.vars ->
  cond:terms ->
  p:Match.Pos.pos ->
  st:term ->
  term ->
  n_occs * ('a, 'b) simple_occs

(*------------------------------------------------------------------*)
(** {1 Proof obligations for name occurrences} *)

(** Given
    - a {!f_fold_occs} function,
    - a context (in particular, that includes the systems we want to use)
    - the environment,
    - a list of sources where we search for occurrences,
    - an [('a,'b) occ_formula] function (which we also use for subsumption),
    - optionally, a [pp_ns] that prints what we look for
     (just for pretty printing),
    computes two list of formulas whose disjunctions respectively mean
    "a bad name occurrence happens" and
    "an [('a,'b) simple_occ] is a collision".

    Alternatively, if [negate] is set to [true],
    the conjunctions mean "no bad occurrence happens" and
    "no collision happens". *)
val occurrence_formulas :
  ?use_path_cond : bool ->
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  ('a, 'b) occ_formula ->
  ('a, 'b) f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms * terms

(** Instance of {!occurrence_formulas} for when we only look for names.
    It is used for the [fresh] tactic. *)
val name_occurrence_formulas :
  ?use_path_cond : bool ->
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  (unit, unit) f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms

(** Returns all found occurrences as well as the formulas,
    for more complex use cases (eg. [intctxt]).
    {b TODO} clarify specification. *)
val occurrence_formulas_with_occs :
  ?use_path_cond : bool ->
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  ('a, 'b) occ_formula ->
  ('a, 'b) f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms * terms * name_occs * ('a, 'b) ext_occs
