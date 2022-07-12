(** Generic functions to search illegal occurrences of names,
    and generate the appropriate proof obligations.
    Building upon Iter and Match.
    For use when writing tactics, eg gdh, fresh. *)

open Term

module TS = TraceSequent

module Hyps = TS.LocalHyps

type lsymb = Theory.lsymb

module MP = Match.Pos
module Sp = MP.Sp
module SE = SystemExpr

(*------------------------------------------------------------------*)
(** Exception raised when a forbidden occurrence of a message variable
    is found. *)
exception Var_found

(** Functions to find all timestamps occurring in a term 
    type of a timestamp occurrence *)
type ts_occ = Term.term Iter.occ

type ts_occs = ts_occ list


(** Return timestamps occuring in macros in a list of terms *)
val get_macro_actions : Constr.trace_cntxt -> Term.terms -> ts_occs


(*------------------------------------------------------------------*)
(** {2 Occurrence of a name} *)

(** information used to remember where an occurrence was found.
    - the name it's in collision with,
    - a subterm where it was found (for printing),
    - optionally the action producing the iocc where
      it was found, for indirect occs *) 
type occ_info = { 
  oi_name    : nsymb; 
  oi_subterm : term; 
  oi_action  : term option;
}

(** constructs an occ_info *)
val mk_oinfo : ?ac:term option -> nsymb -> term -> occ_info

type name_occ = (nsymb * occ_info) Iter.occ
type name_occs = name_occ list


(** constructs a name occurrence *)
val mk_nocc : nsymb -> occ_info -> Vars.vars -> terms -> Sp.t -> name_occ

(** prints a description of the occurrence *)
val pp : Format.formatter -> name_occ -> unit
  
(** prints a description of a subsumed occurrence *)
val pp_sub : Format.formatter -> name_occ -> unit

(*------------------------------------------------------------------*)
(* utility functions for lists of nsymbs *)

(** looks for a name with the same symbol in the list *)
val exists_symb : nsymb -> nsymb list -> bool

(** finds all names with the same symbol in the list *)
val find_symb : nsymb -> nsymb list -> nsymb list

(*------------------------------------------------------------------*)
(* Proof obligations for a name occurrence *)

(** Constructs the formula
    "exists free vars.
      (exists t1.occ_vars. action ≤ t1.occ_cnt || 
       … || 
       exists tn.occ_vars. action ≤ tn.occ_cnt) &&
      conditions of occ && 
      indices of n = indices of occ"
    which will be the condition of the proof obligation when finding the 
    occurrence occ.
    action is the action producing the occ (optional, for direct occs)
    ts=[t1, …, tn] are intended to be the timestamp occurrences in t.
    The free vars of occ.occ_cnt should be in env \uplus occ.occ_vars,
    which is the case if occ was produced correctly
    (ie by Match.fold given either empty (for direct occurrences)
     or iocc_vars (for indirect occurrences).
    Not all free vars of action and condition are there: there may be some indices
    in them that don't appear in the occurrence -> we existentially quantify them. 
    The free vars of ts should be in env.
    Everything is renamed nicely wrt env. *)
val occurrence_formula : ts_occs -> Vars.env -> name_occ -> term


(** Constructs the proof obligation (trace sequent) for a direct or indirect 
   occurrence, stating that it suffices to prove the goal assuming
   the occurrence occ is equal to the name it collides with. *)
val occurrence_sequent : ts_occs -> TS.sequent -> name_occ -> TS.sequent


(*------------------------------------------------------------------*)
(* Functions handling macro expansion in terms, when allowed *)

(* information used to check if a macro can be expanded in a term.
  - the current sequent, for direct occurrences; 
  - the action for the iocc that produced the term, for indirect ones;
  - and in any case the trace context. *)
type expand_info = EI_direct of TS.sequent * Constr.trace_cntxt
                 | EI_indirect of term * Constr.trace_cntxt

(** gets the sequent for the direct occurrence we're looking at *)
val get_sequent : expand_info -> TS.sequent option

(** gets the action for the iocc that produced the term we're looking at *)
val get_action : expand_info -> term option
  
(** gets the trace context *)
val get_context : expand_info -> Constr.trace_cntxt

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
(** given
    - a function find_occs that generates a list of occurrences found in
      a term, expanding macros when possible according to expand_info but not 
      otherwise (undef and maybedef macros will be handled by fold_macro_support);
    - the sequent s of the current goal;
    - the term t where we look for occurrences;
    - optionally, a printer that prints a description of what we're looking for; 
  computes the list of corresponding proof obligations: we now have to prove s
  under the assumption that at least one of the found occurrences must
  be an actual collision.
  Relies on fold_macro_support to look through all macros in the term. *)
val occurrence_sequents :
      ?pp_ns: (unit Fmt.t) option ->
      (se:SE.arbitrary ->
       env:Vars.env ->
       ?fv:Vars.vars ->
       expand_info ->
       term ->
       name_occs) ->
      TS.sequent ->
      Term.term ->
      TS.sequents
  

(*------------------------------------------------------------------*)
(* Functions to look for illegal name occurrences in a term *)

(** type of a function that takes a term, and generates
    a list of occurrences in it, using
     - a continuation unit -> name_occs
       when it does not want to handle the term it's given,
       and just asks to be called again on the subterms
     - a continuation fv -> cond -> p -> se -> st -> term -> name_occs,
       for when it needs to do some work on the term, and needs to
       call fold_bad_occs again on some of its subterms.
    These functions are for use in fold_bad_occs and occurrence_goals.
    They don't need to unfold macros, that's handled separately. *)
type f_fold_occs = 
  (unit -> name_occs) -> (* continuation: give up and try again on subterms *)
  (fv:Vars.vars ->       (* continuation: to be called on strict subterms 
                            (for rec calls) *)
   cond:terms ->
   p:MP.pos ->           
   se:SE.arbitrary ->   
   st:term ->            
   term ->               
   name_occs) ->         
  se:SE.arbitrary ->    (* system at the current position *)
  info:expand_info ->   (* info to expand macros *)
  fv:Vars.vars ->       (* variables bound above the current position *)
  cond:terms ->         (* condition at the current position *)
  p:MP.pos ->           (* current position*)
  st:term ->            (* a subterm we're currently in (for printing purposes) *)
  term ->               (* term at the current position *)
  name_occs             (* found occurrences *)

  
(** given a f_fold_occs function get_bad_occs,
    calls get_bad_occs, is called again when get_bad_occs asks
    for recursive calls on subterms, and handles the case where
    get_bad_occs calls its first continuation (ie gives up)
    by 1) unfolding the term, if it's a macro that can be unfolded
       2) doing nothing, if it's a macro that can't be unfolded
          (in that case, fold_macro_support will generate a separate iocc
          for that)
       2) using Match.Pos.fold_shallow, to recurse on subterms at depth 1. *)
val fold_bad_occs :
  f_fold_occs -> 
  se:SE.arbitrary -> env:Vars.env -> ?fv:Vars.vars -> expand_info ->
  term -> name_occs


(** given
    - a f_fold_occs function get_bad_occs;
    - the sequent s of the current goal;
    - the term t where we look for occurrences;
    - optionally, a printer that prints a description of what 
      we're looking for;
  computes the list of proof obligations: we now have to prove s
  under the assumption that at least one of the found occurrences must
  be an actual collision.*)
val occurrence_goals :
      ?pp_ns: (unit Fmt.t) option ->
      f_fold_occs ->
      TS.sequent ->
      term ->
      TS.sequents
