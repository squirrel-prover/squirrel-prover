(** Sequents used to prove trace properties, aka reachability properties.

    This module implements {!LowSequent.S} with [type form = Term.term]. *)

type trace_sequent

(*------------------------------------------------------------------*)  
include LowSequent.S
  with type hyp_form = Equiv.any_form
   and type conc_form = Equiv.local_form
   and type t = trace_sequent

(*------------------------------------------------------------------*)
(** {2 Sequent type and basic operations} *)

val init : ?no_sanity_check:bool -> env:Env.t -> Term.term -> sequent
  
(** Free variables + var env **toplevel** sanity check *)
val sanity_check : trace_sequent -> unit

(** Project diff-operators occurring in a sequent;
    only makes sense when a sequent for a bi-system has just
    been narrowed to a projected system. *)
val pi : Term.proj -> sequent -> sequent
 
(*------------------------------------------------------------------*)
(** {2 Automated reasoning}

    All these functions only consider local formula hypotheses.
    It could make sense to extend some of them in the future. *)

(** [get_trs s] returns a term rewriting system that corresponds to the set of
    equalities between messages. It can be used to check if an equality is
    implied by the set of messages hypotheses. 
    May timeout. *)
val get_trs : sequent -> Completion.state 

(** See [Constr.query] *)
val query : precise:bool -> t -> Term.Lit.literals -> bool

module Benchmark : sig

    (** [register_query_alternative name f] adds an alternative method
        for solving queries (in a form that subsumes query and
        constraints_valid) which will be benchmarked against the default
        implementation.
        For each call to [query ~precise s q], [f ~precise s (Some q)]
        will be ran and timed and its result (including potential errors)
        will be logged.
        For each call to [constraints_valid s q], [f ~precise:true s None]
        will be similarly executed. *)
    val register_query_alternative :
      string -> (precise:bool -> t -> Term.Lit.literals option -> bool) -> unit

    (** Set position information for benchmark logging purposes. *)
    val set_position : string -> unit

end

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

(** [maximal_elems s ts] returns the maximal elements of the timestamps,
    according to their ordering derived from the hypothesis in [s]. 
    May timeout. *)
val maximal_elems : 
  precise:bool -> sequent -> Term.terms -> 
  Term.terms 

(** [get_all_messages s] returns all the messages appearing at toplevel
    in [s]. *)
val get_all_messages : sequent -> Term.terms