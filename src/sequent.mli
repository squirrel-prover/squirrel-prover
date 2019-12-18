(** This module implement sequents from the sequent calculus. It contains:
    - a set of hypotheses, that can be generic formulas, trace formulas or
   (dis)equalities between messages, and a goal formula;
    - a goal formula;
    - an environment to store all the variables appearing inside the formulas.
*)
open Term
open Bformula
open Formula

(** Hypothesis about messages can be used with the euf_cma axiom, but only
   once,each hypothesis is thus tagged with the following tag. *)
type mess_tag =  { t_euf : bool}

(** This type encapsulate an hypothesis about messages, e.g a (dis)equality
   between messages, along with a tag and a name. *)
type message_hypothesis

(** [set_euf b mh], given an hypothesis about messages mh, set its tag to [b].*)
val set_euf : bool -> message_hypothesis -> message_hypothesis

(** {2 Main sequent type and basic operations} *)

type sequent

val pp : Format.formatter -> sequent -> unit

(** [init formula] returns a sequent with an empty set of hypothesis, and the
   given formula as goal. *)
val init : formula -> sequent

(** [add_trace_formula tf s] returns the sequent [s] with [tf] added to its
    hypothesis. *)
val add_trace_formula : ?prefix:string -> trace_formula -> sequent -> sequent

(** [add_trace_formula f s] returns the sequent [s] with [f] added to its
    hypothesis. *)
val add_formula : ?prefix:string -> formula -> sequent -> sequent

(** [set_env e s] set the environment of the sequent ot the given environment.
*)
val set_env : Vars.env -> sequent -> sequent

(** [get_env s] returns the environment of the sequent. *)
val get_env : sequent -> Vars.env

(** [set_formula f s] set the goal formula of the sequent to [f]. *)
val set_formula : formula -> sequent -> sequent

(** [get_formula s] returns the goal formula of the sequent. *)
val get_formula : sequent -> formula

(** [select_message_hypothesis name s update] gives back the message
   (dis)equality corresponding to the given name inside the hypothesis of [s],
   and also [s] after applying the [update] function to the selected
   hypothesis. *)
val select_message_hypothesis : string -> sequent -> (message_hypothesis ->
   message_hypothesis) -> (sequent * term_atom)

(** {2 Sequent logical operations} *)

(** [is_hypothesis f s] returns true if the formula appears inside the hypotesis
   of the sequent [s]. Might be used to prove the validity of a sequent, if its
   formula appears inside its hypothesis. *)
val is_hypothesis : formula -> sequent -> bool

(** [get_trs s] returns a term rewriting system that corresponds to the set of
   equalities between messages. It can be used to check if an equality is
   implied by the set of messages hypotheses. *)
val get_trs : sequent -> sequent * Completion.state

(** If [message_atoms_valid s] returns [true] then (dis)equalities over
  * messages on both sides of the sequents make the sequent valid. *)
val message_atoms_valid : sequent -> bool

(** [constraints_valid s] returns true if constraints make the sequent valid,
  * taking into account constraint trace formula hypotheses and atomic
  * constraint conclusion. *)
val constraints_valid : sequent -> bool

(** [get_all_terms s] return all the term appearing inside the messages
   hypothesis of [s]. *)
val get_all_terms : sequent -> Term.term list

(** [get_ts_equalities s] return all the equalities between timestamps
       derivable from its hypothesis. *)
val get_ts_equalities : sequent -> timestamp list list

(** [maximal_elems s ts] returns the maximal elements of the timestamps,
   according to their ordering derived from the hypothesis in [s]. *)
val maximal_elems : sequent -> timestamp list -> timestamp list
