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
(* Functions handling macro expansion in terms, when allowed *)

(* information used to check if a macro can be expanded in a term:
   - the trace context
   - a tag indicating whether the occurrence is direct or indirect
     (for an indirect occurrence, the action producing it is recorded) *)
type occ_type =
  | EI_direct
  | EI_indirect of term

type expand_info = occ_type * Constr.trace_cntxt

(** expands t if it is a macro and we can check that its timestamp happens
    using info (not recursively).
    Returns Some t' if t expands to t', None if no expansion was performed *)
val expand_macro_check_once : expand_info -> term -> term option

(** expands t as much as possible, recursively
    (only at toplevel, not in subterms) *)
val expand_macro_check_all : expand_info -> term -> term

(** returns (u, v) such that t = (u = v), or None if not possible.
    (unfolds the macros when possible) *) 
val destr_eq_expand : expand_info -> term -> (term * term) option



(*------------------------------------------------------------------*)
(** Functions to find all timestamps occurring in a term 
    type of a timestamp occurrence *)
type ts_occ = Term.term Iter.occ

type ts_occs = ts_occ list


(** Return timestamps occuring in macros in a list of terms *)
val get_macro_actions : (Term.term * expand_info) list -> ts_occs


(*------------------------------------------------------------------*)
(** {2 Occurrence of a name} *)

type n_occ = nsymb Iter.occ

(** constructs a name occurrence *)
val mk_nocc :
  nsymb ->
  Vars.vars ->
  terms ->
  Sp.t ->
  n_occ


(*------------------------------------------------------------------*)
(* Functions to look for illegal name occurrences in a term *)

(** type of a function that takes a term, and generates
    a list of occurrences in it, each with the name it collides with
    and a subterm it was found in, using
    - a continuation unit -> (n_occ * nsymb * term) list
       when it does not want to handle the term it's given,
       and just asks to be called again on the subterms
    - a continuation fv -> cond -> p -> se -> st -> term -> (n_occ * nsymb * term) list,
       that calls the function again on the given parameters,
       for when it needs to do finer things
       (typically handle some of the subterms manually, and call this continuation
          on the remaining ones,
        or handle subterms at depth 1 by hand, and call the continuation on subterms at depth 2).
      Functions of this type don't need to unfold macros, that's handled separately. *)
type f_fold_occs = 
  (unit -> (n_occ * nsymb * term) list) -> (* continuation: give up and try again on subterms *)
  (fv:Vars.vars ->       (* continuation: to be called on strict subterms (for rec calls) *)
   cond:terms ->
   p:MP.pos ->           
   info:expand_info ->
   st:term ->            
   term ->               
   (n_occ * nsymb * term) list)->         
  info:expand_info ->  (* info to expand macros, incl. system at current pos *)
  fv:Vars.vars ->      (* variables bound above the current position *)
  cond:terms ->        (* condition at the current position *)
  p:MP.pos ->          (* current position*)
  st:term ->           (* a subterm we're currently in (for printing purposes) *)
  term ->              (* term at the current position *)
  (n_occ * nsymb * term) list (* found occurrences *)


(*------------------------------------------------------------------*)
(* Proof obligations for name occurrences *)

(* given
   - a f_fold_occs function (see above)
   - a context (in particular, that includes the systems we want to use)
   - the environment
   - a list of sources where we search for occurrences
   - optionally, a pp_ns that prints what we look for (just for pretty printing)
   - a flag negate == do we take the formula's negation (default false)
     computes a list of formulas whose disjunction means "a bad occurrence happens"
     (or, alternatively, if negate is set to true,
     whose conjunction means "no bad occurrence happens") *)
val occurrence_formulas :
  ?negate : bool ->
  ?pp_ns: (unit Fmt.t) option ->
  f_fold_occs ->
  Constr.trace_cntxt ->
  Vars.env ->
  terms ->
  terms
