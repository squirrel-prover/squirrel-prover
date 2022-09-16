(** Generic functions to search illegal occurrences of names,
    and generate the appropriate proof obligations.
    Building upon Iter and Match.
    For use when writing tactics, eg gdh, fresh. *)

open Term

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp
module SE = SystemExpr



(*------------------------------------------------------------------*)
(** Generic types and functions to handle occurrences of anything,
    with associated data and conditions, source timestamps, etc. *)
(* probably somewhat redundant with Iter.occ… but more specific to the use case here *)


(** Simple occurrence of an element of type 'a, with additional data of type 'b *)
(* Remarks:
   1) we could store a position in the term where the occ was, as in Iter.occ,
      but we don't use it anywhere for now
   2) we could store the fset at the point where the occ was found, which would
      be more precise (we would need to prove the goal for the occ only in that fset)
      (though since fold_macro_support does not give us the fset where the iocc is,
      we would still potentially be a little imprecise).
      we'll see if that's an issue later, for now we don't do that. *) 
type ('a, 'b) simple_occ = 
  {so_cnt     : 'a;        (* content of the occurrence *)
   so_coll    : 'a;        (* thing it potentially collides with *)
   so_ad      : 'b;        (* additional data, if needed *)
   so_vars    : Vars.vars; (* variables bound above the occurrence *)
   so_cond    : terms;     (* condition above the occurrence *)
   so_subterm : term;      (* a subterm where the occurrence was found (for printing) *)
  }

type ('a, 'b) simple_occs = (('a, 'b) simple_occ) list


(** constructs a simple occurrence *)
val mk_simple_occ : 'a -> 'a -> 'b -> Vars.vars -> terms -> term -> ('a, 'b) simple_occ


(** Type of a timestamp occurrence *)
(* maybe does not need to be exposed *)
type ts_occ = (term, unit) simple_occ
type ts_occs = ts_occ list


(** Type of empty simple occurrences (used as dummy parameter when they are not needed) *)
type empty_occ = (unit, unit) simple_occ
type empty_occs = empty_occ list


(** Label indicating whether an occurrence is direct or indirect, and
   if so which action produced it *)
type occ_type =
  | EI_direct
  | EI_indirect of term


(** Functions to turn content and data into terms, so they can be 
    compared by matching. (we could have one function 'a -> 'a -> 'b -> term 
    instead, if needed later *)
type ('a, 'b) converter = { conv_cnt:'a -> term; conv_ad: 'b -> term }

(** Converter for names *)
val name_converter : (nsymb, unit) converter

(** Dummy converter for empty occurrences *)
val empty_converter : (unit, unit) converter

(** Extended occurrence, with additional info about where it was found *)
type ('a, 'b) ext_occ =
  {eo_occ       : ('a, 'b) simple_occ;
   eo_occtype   : occ_type;             (* direct/indirect+action *)
   eo_source    : terms;                (* original term where the occ was found *) 
   eo_source_ts : ts_occs }             (* timestamps occurring in the source term *)

type ('a, 'b) ext_occs = (('a, 'b) ext_occ) list



(*------------------------------------------------------------------*)
(** Occurrence subsumption/inclusion functions not exposed, we'll see if they need to be *)


(*------------------------------------------------------------------*)
(* Functions handling macro expansion in terms, when allowed *)

(* information used to check if a macro can be expanded in a term:
   - a tag indicating whether the occurrence is direct or indirect
     (for an indirect occurrence, the action producing it is recorded)
   - the trace context *)
type expand_info = occ_type * Constr.trace_cntxt

(** expands t if it is a macro and we can check that its timestamp happens
    using info (not recursively).
    Returns Some t' if t expands to t', None if no expansion was performed *)
val expand_macro_check_once : expand_info -> term -> term option

(** expands t as much as possible, recursively
    (only at toplevel, not in subterms) *)
val expand_macro_check_all : expand_info -> term -> term



(*------------------------------------------------------------------*)
(** Returns all timestamps occuring in macros in a list of terms.
    Should only be used when sources are directly occurring,
    not themselves produced by unfolding macros *)
val get_macro_actions : Constr.trace_cntxt -> term list -> ts_occs


(*------------------------------------------------------------------*)
(** Occurrence of a name *)

type n_occ = (nsymb, unit) simple_occ
type n_occs = n_occ list

type name_occ = (nsymb, unit) ext_occ
type name_occs = name_occ list

(** Constructs a name occurrence *)
val mk_nocc : 
  nsymb -> (* name *)
  nsymb -> (* name it collides with *)
  Vars.vars -> (* vars bound above *)
  terms -> (* condition above *)
  term -> (* subterm (for printing) *)
  n_occ


(*------------------------------------------------------------------*)
(* Functions to look for illegal name occurrences in a term *)

(** Type of a function that takes a term, and generates a list of name occurrences in it.
    Also returns a list of ('a, 'b) simple occurrences, used to record
    information gathered during the exploration of the term
    (typically collisions between other things than names, but with the 'b so_ad field,
    can record anything useful).
    Uses
    - a continuation unit -> n_occs * 'a, 'b simple_occs
       when it does not want to handle the term it's given,
       and just asks to be called again on the subterms
    - a continuation fv -> cond -> p -> se -> st -> term -> n_occs * ('a,'b) simple_occs,
       that calls the function again on the given parameters,
       for when it needs to do finer things
       (typically handle some of the subterms manually, and call this continuation
          on the remaining ones,
        or handle subterms at depth 1 by hand, and call the continuation on subterms at depth 2).
      Functions of this type don't need to unfold macros, that's handled separately. *)
type ('a, 'b) f_fold_occs = 
  (unit -> n_occs * ('a, 'b) simple_occs) -> (* continuation: give up and try again on subterms *)
  (fv:Vars.vars ->       (* continuation: to be called on strict subterms (for rec calls) *)
   cond:terms ->
   p:MP.pos ->           
   info:expand_info ->
   st:term ->
   term ->
   n_occs * ('a, 'b) simple_occs)->         
  info:expand_info ->  (* info to expand macros, incl. system at current pos *)
  fv:Vars.vars ->      (* variables bound above the current position *)
  cond:terms ->        (* condition at the current position *)
  p:MP.pos ->          (* current position*)
  st:term ->           (* a subterm we're currently in (for printing purposes) *)
  term ->              (* term at the current position *)
  n_occs * ('a, 'b) simple_occs (* found name occurrences, and other occurrences *)



(*------------------------------------------------------------------*)
(* Proof obligations for name occurrences *)

(** Type of a function generating a formula meant to say
    "the occurrence is actually a collision" (or its negation) *)
type ('a, 'b) occ_formula =
  negate:bool ->
  'a -> (* occurrence content *)
  'a -> (* what it potentially collides with *)
  'b -> (* associated data *)
  term

(** occ_formula for name occurrences *)
val name_occ_formula : (nsymb, unit) occ_formula

(** Dummy occ_formula for empty occurrences *)
val empty_occ_formula : (unit, unit) occ_formula

(** given
   - a f_fold_occs function (see above)
   - a context (in particular, that includes the systems we want to use)
   - the environment
   - a list of sources where we search for occurrences
   - conversion (for detecting duplicate) and formula functions for 'a, 'b occurrences
   - optionally, a pp_ns that prints what we look for (just for pretty printing)
   
   computes two list of formulas whose disjunctions respectively mean
   "a bad name occurrence happens" and "an 'a, 'b occurrence is a collision"
      (or, alternatively, if negate is set to true,
   whose conjunction means "no bad occurrence happens" and "no collision happens") *)
val occurrence_formulas :
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  ('a, 'b) converter ->
  ('a, 'b) occ_formula ->
  ('a, 'b) f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms * terms

(** occurrence_formula instantiated for the case where we only look for names *)
(** eg fresh *)
val name_occurrence_formulas :
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  (unit, unit) f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms


(** variant of occurrence_formula that returns
    all found occurrences as well as the formulas,
    for more complex use cases (eg intctxt) *)
val occurrence_formulas_with_occs :
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  ('a, 'b) converter ->
  ('a, 'b) occ_formula ->
  ('a, 'b) f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms * terms * name_occs * ('a, 'b) ext_occs
