module SE = SystemExpr
module MP = Match.Pos

module TraceHyps = Hyps.TraceHyps
module PathCond  = Iter.PathCond

(*------------------------------------------------------------------*)
(** Overview:
    The [Occurrences] module provides ways to easily search for occurrences
    of anything in a term.

    - Users need to provide a module of type [OccContent],
      containing the type of the things they want to search for, and a few
      operations on this type.

    - The MakeSearch functor will take that module as a parameter,
      and produce a module of type [OccurrenceSearch],
      containing a function [find_all_occurrences].

    - Users need to provide that function with a [get_bad_occs] function.
      This function does not need to worry about unfolding macros, iterating
      through the term, or looking for indirect occurrences. 
      It only looks for the occurrences at top level in a term.
      It has access to two continuations :
      * one to "give up": return no occurrences, and ask to be called
        again on all subterms. suffices in most simple cases.
      * a second one, more precise, asks to be called recursively on
        some of the subterms only, for more complex cases.

    - [find_all_occurrences] will then take care of iterating through all
      direct and indirect terms, and return all found occurrences.

    - A second functor, [MakeFormulas], will take a module of type [ExtOcc]
      (that is built by [MakeSearch]), and provide a function to generate
      the proof goals associated to the list of occurrences found.
      Users may of course decide to only call that function on some of the
      found occurrences.
*)

(*------------------------------------------------------------------*)
(** Interprets [phi] as [phi_1 /\ … /\ phi_n]
    and reconstructs it to simplify trivial equalities. *)
val clear_trivial_equalities : Term.term -> Term.term

(*------------------------------------------------------------------*)
(** {2 Occurrence contents} *)

(** Module containing the type of the contents of occurrences
    we will look for, and some operations on this type. *)
module type OccContent = sig
  (** Type of the thing for which we want occurrences *)
  type content

  (** Additional data to be stored in the occurrences *)
  type data

  (** Type of a function generating a formula meant to say
      "the occurrence is actually a collision" (or its negation).

      Arguments are:
      - occurrence content,
      - what the occurrence potentially collides with,
      - the associated data.

      We also use this formula to compute occurrence subsumption:
      we turn occurrences to terms using it, and then
      o2 subsumes o1 if o1's term is an instantiation of o2's. *)
  val collision_formula :
    negate:bool -> content -> content -> data -> Term.term

  (** Applies a substitution to an occurrence content *)
  val subst_content : Term.subst -> content -> content

  (** Applies a substitution to an occurrence additional data *)
  val subst_data : Term.subst -> data -> data

  (** Printing function for occurrence contents *)
  val pp_content : Format.formatter -> content -> unit

  (** Printing function for occurrence data *)
  val pp_data : Format.formatter -> data -> unit

end

(*------------------------------------------------------------------*)
(** Predefined instance of [OccContent] for timestamps,
    plus a dummy occurrence with no content *)

module TSContent : OccContent 
  with type content = Term.term
   and type data = unit

module EmptyContent : OccContent 
  with type content = unit
   and type data = unit

(*------------------------------------------------------------------*)
(** {2 Simple occurrences} *)

(** Tag indicating whether an occurrence is direct,
    or indirectly caused by some action given as a {!Term.term}. *)
type occ_type =
  | EI_direct
  | EI_indirect of Term.term

(** Applies a substitution to an {!occ_type}. *)
val subst_occtype : Term.subst -> occ_type -> occ_type

(*------------------------------------------------------------------*)
(** Signature of a module for simple occurrences.
    Contains an OccContent submodule, defining what types occurrences contain.
    They contain a content, and a value of the same type with which it
    could collide (that value is the one we search occurrences of).
    They also store additional information such as the variables
    bound above the occurrence. *)
module type SimpleOcc = sig

  (** The content occurrences store *)
  module OC : OccContent

  type content = OC.content

  type data = OC.data

  (* Remarks:
     - We could store a position in the term where the occ was, as in Iter.occ,
       but we don't use it anywhere for now
     - We could store the fset at the point where the occ was found, which would
       be more precise (we would need to prove the goal for the occ only in that
       fset). Since fold_macro_support does not give us the fset where the iocc
       is, we would still potentially be a little imprecise.
       We'll see if that's an issue later, for now we don't do that. *)
  (** Simple occurrence of an element of type [content],
      with additional data of type [data]. *)
  type simple_occ =
    {so_cnt     : content;  (** content of the occurrence *)
     so_coll    : content;  (** thing it potentially collides with *)
     so_ad      : data;     (** additional data, if needed *)
     so_vars    : Vars.vars;   (** variables bound above the occurrence *)
     so_cond    : Term.terms;  (** condition above the occurrence *)
     so_occtype : occ_type;    (** occurrence type *)
     so_subterm : Term.term;   (** a subterm where the occurrence was found
                                   (for printing) *)
    }


  type simple_occs = simple_occ list

  (*------------------------------------------------------------------*)
  (** Constructs a simple occurrence.
      alpha-renames the variables given in parameters, to avoid confusion. 
      Hence it is assumed fv contains all variables occurring in the content
      and data that are bound above the occurrence. *)
  val mk_simple_occ :
    content -> content -> data ->
    Vars.vars -> Term.terms -> occ_type -> Term.term ->
    simple_occ

  (*------------------------------------------------------------------*)
  (** Auxiliary function to check if all instances of [o1]
      are instances of [o2]. 
      Returns the matching substitution, so that it can be reused for 
      [ext_occ_incl].
      We use the occ_formula to turn its contents into a term.
      this means we subsume occurrences that are not actually equal
      as long as they produce the same formula in the end.
      In principle it should be fine, if not just give
      a different occ_formula that doesn't simplify anything. *)
  val aux_occ_incl :
    Symbols.table -> SE.fset -> ?mv:Match.Mvar.t ->
    simple_occ -> simple_occ -> Match.Mvar.t option

  (** Occurrence subsumption/inclusion.
      Specification:
        occ1 included in occ2 MUST mean that
          (occ1 is a collision) \/ (occ2 is a collision) <=>
          (occ2 is a collision)
      so that we only need to look at occ2.
      For this, occ1 must be an instance of occ2,
      in an instance of its action, with a STRONGER condition
       (not weaker, watch out we've made that mistake before) *)
  val occ_incl :
    Symbols.table -> SE.fset -> simple_occ -> simple_occ -> bool

  (** Removes subsumed occurrences from a list *)
  val clear_subsumed :
    Symbols.table -> SE.fset -> simple_occs -> simple_occs

  (** Prints a description of the occurrence *)
  val pp : Format.formatter -> simple_occ -> unit
end


(** Functor to produce a SimpleOcc module from an OccContent *)
module MakeSO : functor (OC:OccContent) -> (SimpleOcc with module OC = OC)

(*------------------------------------------------------------------*)
(** module for timestamp occurrences *)
module TSOcc : (SimpleOcc with module OC = TSContent)

type ts_occ  = TSOcc.simple_occ
type ts_occs = TSOcc.simple_occs

(*------------------------------------------------------------------*)
(** module for empty simple occurrences
    (used as dummy parameter when they are not needed). *)
module EmptyOcc : (SimpleOcc with module OC = EmptyContent)

type empty_occ  = EmptyOcc.simple_occ
type empty_occs = EmptyOcc.simple_occs

(*------------------------------------------------------------------*)
(** {2 Extended occurrences} *)

(** Module for extended occurrences.
    Contains as a submodule a SimpleOcc module.
    An extended occurrence is a simple occurrence +
    some data on timestamps and sources.
    We separate them from simple occurrences because
    1) they contain ts_occs which are themselves simple occs
    2) users do not need to worry about constructing them,
    they only need to construct simple occurrences. *)
module type ExtOcc = sig

  (** Submodule: the [SimpleOcc] we extend *)
  module SO : SimpleOcc

  type simple_occ = SO.simple_occ

  (** Occurrence with additional info about where it was found. *)
  type ext_occ = {
    eo_occ       : simple_occ;
    eo_source    : Term.terms;     
    (** Original terms where the occurrence was found. *)
    eo_source_ts : ts_occs; 
    (** Timestamps occurring in the source terms. *)
    eo_path_cond : Iter.PathCond.t; 
    (** Path condition on the timestamps [τ] at which the occurrence
        can occur: 
        for any source timestamp [τ_src] (in [eo_sources_ts]), 
        [path_cond τ τ_src] *)
  }

  type ext_occs = ext_occ list

  (** Inclusion for extended occurrences:
      Checks if all instances of [occ1] are instances of [occ2]
      (ie [occ2] subsumes [occ1]). *)
  val ext_occ_incl :
    Symbols.table -> SE.fset -> ext_occ -> ext_occ -> bool

  (** Removes subsumed extended occurrences from a list *)
  val clear_subsumed :
    Symbols.table -> SE.fset -> ext_occs -> ext_occs

  (** Prints a description of the occurrence. *)
  val pp : Format.formatter -> ext_occ -> unit

  (** Prints a list of occurrences *)
  val pp_occs : Format.formatter -> ext_occs -> unit

end

(** Functor to create an ExtOcc from a SimpleOCc *)
module MakeEO :
  functor (SO:SimpleOcc) -> (ExtOcc with module SO = SO)


(*------------------------------------------------------------------*)
(** {2 Macro expansion}
    Functions handling macro expansion in terms, when allowed. *)

(** Information on a position when iterating through a term *)
type pos_info =
  { pi_pos     : MP.pos;             (** the position *)
    pi_occtype : occ_type;           (** are we in a direct or indirect term *)
    pi_trctxt  : Constr.trace_cntxt; (** system+table at the position *)
    pi_vars    : Vars.vars;          (** variables bound above the position *)
    pi_cond    : Term.terms;         (** conditions above the position *)
    pi_subterm : Term.term;          (** subterm of the position (for printing) *)
  }

(** Information used to check if a macro can be expanded in a term:
    - a tag indicating the occurrence type (and provenance);
    - the trace context. *)
type expand_info = occ_type * Constr.trace_cntxt

(** Extracts the expand_info from the pos_info *)
val get_expand_info : pos_info -> expand_info

(** Expands a term [t] if it is a macro
    and we can check that its timestamp happens
    using [info] (not recursively).
    Returns [Some t'] if [t] expands to [t'],
    [None] if no expansion has been performed. *)
val expand_macro_check_once : expand_info -> Term.term -> Term.term option

(** Expands term as much as possible, recursively
    (only at toplevel, not in subterms). *)
val expand_macro_check_all : expand_info -> Term.term -> Term.term

(** Returns all timestamps occuring in macros in a list of terms.
    Should only be used when sources are directly occurring,
    not themselves produced by unfolding macros. *)
val get_macro_actions : Constr.trace_cntxt -> Term.terms -> ts_occs

(*------------------------------------------------------------------*)
(** {2 Occurrence search} *)
  
(** Module containing functions to search for occurrences of the given type
    in a term, iterating through the term and indirect occurrences,
    unfolding macros. *)
module type OccurrenceSearch = sig
  (** Submodule: the [ExtOcc] we look for *)
  module EO : ExtOcc

  type simple_occ = EO.simple_occ
  type simple_occs = simple_occ list
  type ext_occ = EO.ext_occ
  type ext_occs = ext_occ list

  (** Type of a function that takes a term, and generates
      a list of simple occurrences in it.
      
      Uses:
      - A continuation of type [unit -> simple_occs]:
        to "give up", ie do nothing and
        and just ask to be called again on the subterms.
      - A continuation of type [pos_info -> term -> simple_occs]
        to call the function again on the given parameters.
        Useful when we need to do finer things
        (typically handle some of the subterms manually,
         and call this continuation on the remaining ones,
         or handle subterms at depth 1 by hand,
         and call the continuation on subterms at depth 2).
      
      Functions of this type don't need to unfold macros,
      which are handled separately. *)
  type f_fold_occs =
    (unit -> simple_occs) ->
    (pos_info -> Term.term -> simple_occs) ->
    pos_info ->
    Term.term ->
    simple_occs
    
  (** Given a [f_fold_occs],
      computes the list of all occurrences in the given source terms.
      Takes care of macro expansion and going through all terms,
      using [fold_macro_support] and [map_fold]. *)
  val find_all_occurrences :
    mode:Iter.allowed_constants -> (* allowed sub-terms without further checks *)
    ?pp_ns:unit Fmt.t option -> (* printing searched for occurrences *)
    f_fold_occs ->
    TraceHyps.hyps ->
    Constr.trace_cntxt ->
    Env.t ->
    Term.terms ->
    ext_occs
end

(** Functor to construct an OccurrenceSearch for a given OccContent. *)
module MakeSearch :
  functor (OC:OccContent) -> (OccurrenceSearch with module EO.SO.OC = OC)

(** [time_formula τ ts_occs] constructs the formula:

      [(∃ v1. path_cond τ ts1 ∨ … ∨ ∃ vn. path_cond τ tsn)]

    where [vi], [tsi] are the variables and content of [ts_occ]. 
    (for example, [path_cond x y] can be [x ≤ y]). *)
val time_formula : Term.term -> ?path_cond:PathCond.t -> ts_occs -> Term.term

(*------------------------------------------------------------------*)
(** {2 Formula construction and simplification} *)

(** Module to containing functions to produce formulas (proof goals)
    expressing that extended occurrences of the given type are
    indeed collisions (or alternately, that they are not) *)
module type OccurrenceFormulas = sig
  type ext_occ
  type ext_occs = ext_occ list

  (** Constructs the formula
      "exists free vars.
        (exists t1.occ_vars. action ≤ t1.occ_cnt ||
         … ||
         exists tn.occ_vars. action ≤ tn.occ_cnt) &&
        conditions of occ &&
        the occ is a collision"
      (this last part produced by [phiocc]) which will be the condition of the 
      proof obligation when finding the occurrence [occ].

      - [action] is the action producing the occurrence [occ] (for indirect 
        occurrences).
      - [ts = \[t1; …; tn\]] are the timestamp occurrences in [t].
      - The free vars of [occ.occ_cnt], [action], and [cond] not bound
        in the sequent's env should be in [occ.occ_vars],
        which is the case if [occ] was produced correctly
        (i.e. by [Match.fold] given either empty (for direct occurrences)
        or [iocc_vars] (for indirect occurrences)).
      - The free vars of [ts] should be all be bound in the sequent's env.

      If [negate] is set to [true], returns instead the negation of that formula. *)
  val occurrence_formula :
    ?use_path_cond:bool -> negate:bool -> ext_occ -> Term.term
end


(** Functor to construct an OccurrenceFormulas for a given ExtOcc. *)
module MakeFormulas :
  functor (EO:ExtOcc) ->
    (OccurrenceFormulas with type ext_occ = EO.ext_occ)


(*------------------------------------------------------------------*)
(** {2 Instantiation of all modules for searching name occurrences} *)

(** Module to manipulate names more conveniently *)
module Name :
sig
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

  (** checks if t contains a name w/ same symb. as n (w/o expanding macros) *)
  val has_name : t -> Term.term -> bool
end

(*------------------------------------------------------------------*)
(** [OccurrenceContent], [OccurrenceSearch], [OccurrenceFormulas]
    for occurrences of names *)

module NameOC : OccContent 
  with type content = Name.t
   and type data = unit

module NameOccSearch : OccurrenceSearch 
  with module EO.SO.OC = NameOC
                                               
module NameOccFormulas : OccurrenceFormulas 
  with type ext_occ = NameOccSearch.ext_occ
                                               
(*------------------------------------------------------------------*)
(** Utility:
    finds all names in the list with the same symbol as the given name,
    returns the corresponding simple occs *)
val find_name_occ :
  Name.t -> Name.t list -> pos_info ->
  NameOccSearch.simple_occs

