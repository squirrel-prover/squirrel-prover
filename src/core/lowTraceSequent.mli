(** Sequents used to prove trace properties, aka reachability properties.

    This module implements {!LowSequent.S} with [type form = Term.term]. *)

type trace_sequent

(** Wrapper for manipulating local hypotheses only. *)
module LocalHyps : Hyps.S1
  with type hyp = Equiv.local_form
   and type hyps := trace_sequent

(*------------------------------------------------------------------*)  
include LowSequent.S
  with type hyp_form = Equiv.any_form
   and type conc_form = Equiv.local_form
   and type t = trace_sequent

(*------------------------------------------------------------------*)
(** {2 Sequent type and basic operations} *)

val init : env:Env.t -> Term.term -> sequent
  
(** Free variables + var env **toplevel** sanity check *)
val sanity_check : trace_sequent -> unit

(** Project diff-operators occurring in a sequent;
  * only makes sense when a sequent for a bi-system has just
  * been narrowed to a projected system. *)
val pi : Term.proj -> sequent -> sequent
 
(*------------------------------------------------------------------*)
(** {2 Automated reasoning}
  *
  * All these functions only consider local formula hypotheses.
  * It could make sense to extend some of them in the future. *)

(** [get_trs s] returns a term rewriting system that corresponds to the set of
    equalities between messages. It can be used to check if an equality is
    implied by the set of messages hypotheses. 
    May timeout. *)
val get_trs : sequent -> Completion.state 

(** See [Constr.query] *)
val query : precise:bool -> t -> Term.Lit.literals -> bool

val query_happens : precise:bool -> t -> Term.term -> bool

(** If [message_atoms_valid s] returns [true] then (dis)equalities over
    terms on both sides of the sequents make the sequent valid.
    May timeout. *)
val eq_atoms_valid : sequent -> bool 

(** [constraints_valid s] returns true if constraints make the sequent valid,
    taking into account constraint trace formula hypotheses and atomic
    constraint conclusion.
    May timeout. *)
val constraints_valid : sequent -> bool 

(** [get_ts_equalities s] returns all the equalities between timestamps
    derivable from its hypothesis. 
    May timeout. *)
val get_ts_equalities :
  precise:bool -> sequent -> Term.terms list

(** [get_ind_equalities s] returns all the equalities between indices
    derivable from its hypothesis. 
    May timeout. *)
val get_ind_equalities :
  precise:bool -> sequent -> Vars.vars list 

(** [maximal_elems s ts] returns the maximal elements of the timestamps,
    according to their ordering derived from the hypothesis in [s]. 
    May timeout. *)
val maximal_elems : 
  precise:bool -> sequent -> Term.terms -> 
  Term.terms 

(** [get_all_messages s] returns all the messages appearing at toplevel
    in [s]. *)
val get_all_messages : sequent -> Term.terms

(** [literals_unsat_smt] checks whether the conclusion of the sequent follows
    from some "simple" literals in the hypotheses + the formulas declared by
    "hint smt" *)
val literals_unsat_smt : ?slow:bool -> sequent -> bool
