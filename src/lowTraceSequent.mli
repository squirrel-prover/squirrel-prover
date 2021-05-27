(** This module implement sequents used to prove trace properties.
    A sequent is made of:
    - a set of hypotheses;
    - a goal formula;
    - an environment containing the sequent free variables.
*)

module L = Location

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)  
include LowSequent.S with type form = Term.message

(*------------------------------------------------------------------*)
(** {2 Sequent type and basic operations} *)

val init : 
  system:SystemExpr.system_expr -> 
  table:Symbols.table ->
  hint_db:Hint.hint_db ->
  ty_vars:Type.tvars ->
  env:Vars.env ->
  goal:Term.message ->
  sequent
  
(** Project diff-operators occurring in a sequent;
  * only makes sense when a sequent for a bi-system has just
  * been narrowed to a projected system. *)
val pi : Term.projection -> sequent -> sequent
 
(*------------------------------------------------------------------*)
(** {2 Automated reasoning} *)

(** [get_trs s] returns a term rewriting system that corresponds to the set of
    equalities between messages. It can be used to check if an equality is
    implied by the set of messages hypotheses. 
    May timeout. *)
val get_trs : sequent -> Completion.state 

(** See [Constr.query] *)
val query : precise:bool -> t -> Constr.trace_literal list -> bool

val query_happens : precise:bool -> t -> Term.timestamp -> bool

(** If [message_atoms_valid s] returns [true] then (dis)equalities over
  * terms on both sides of the sequents make the sequent valid. 
  * May timeout. *)
val eq_atoms_valid : sequent -> bool 

(** [constraints_valid s] returns true if constraints make the sequent valid,
  * taking into account constraint trace formula hypotheses and atomic
  * constraint conclusion. 
  * May timeout. *)
val constraints_valid : sequent -> bool 

(** [get_ts_equalities s] returns all the equalities between timestamps
    derivable from its hypothesis. 
    May timeout. *)
val get_ts_equalities :
  precise:bool -> sequent -> Term.timestamp list list

(** [get_ind_equalities s] returns all the equalities between indices
    derivable from its hypothesis. 
    May timeout. *)
val get_ind_equalities :
  precise:bool -> sequent -> Vars.index list list 

(** [maximal_elems s ts] returns the maximal elements of the timestamps,
    according to their ordering derived from the hypothesis in [s]. 
    May timeout. *)
val maximal_elems : 
  precise:bool -> sequent -> Term.timestamp list -> 
  Term.timestamp list 


(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** [get_all_terms s] returns all the messages appearing at toplevel
  * in [s]. *)
val get_all_messages : sequent -> Term.message list

val reach_to_form :             Term.message -> form
val form_to_reach : ?loc:L.t -> form -> Term.message