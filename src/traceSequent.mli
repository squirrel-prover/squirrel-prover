(** This module implement sequents used to prove trace properties.
    A sequent is made of:
    - a set of hypotheses;
    - a goal formula;
    - an environment containing the sequent free variables.
*)

open Term

module Args = TacticsArgs
  
(*------------------------------------------------------------------*)
(** {2 Sequent type and basic operations} *)

type t
type sequent = t

val pp : Format.formatter -> sequent -> unit

val init : 
  system:SystemExpr.system_expr -> 
  table:Symbols.table ->
  ty_vars:Type.tvars ->
  env:Vars.env ->
  goal:Term.message ->
  sequent
  
(** Get the system which the sequent is reasoning about. *)
val system : sequent -> SystemExpr.system_expr

(** Get the symbol table of the sequent. *)
val table : sequent -> Symbols.table

(** Change the system of a sequent. *)
val set_system : SystemExpr.system_expr -> sequent -> sequent

(** Change the table of a sequent. *)
val set_table : Symbols.table -> sequent -> sequent

val set_ty_vars : Type.tvar list -> sequent -> sequent

(** Project diff-operators occurring in a sequent;
  * only makes sense when a sequent for a bi-system has just
  * been narrowed to a projected system. *)
val pi : Term.projection -> sequent -> sequent

(** [set_env e s] returns a new sequent with
  * the environment set to [e]. *)
val set_env : Vars.env -> sequent -> sequent

(** [env s] returns the environment of the sequent. *)
val env : sequent -> Vars.env

val ty_vars : sequent -> Type.tvar list

(** Set the goal of the sequent. *)
val set_goal : message -> sequent -> sequent

(** Returns the goal of the sequent. *)
val goal : sequent -> message


(*------------------------------------------------------------------*)
(** {2 Hypotheses} *)

(** Built on top of [Hyps.H]. 
    
    Remark on:
    - [val add : Args.naming_pat -> formula -> sequent -> sequent]
    
    [add id f s] returns the sequent [s] with [f] added to its hypotheses. 
    The new sequent will be automatically enriched with equalities 
    expressing relevant macro definitions, as well as conditions of all 
    named actions that are assumed to happen. *)
module Hyps : Hyps.HypsSeq with type hyp = Term.message and type sequent = t

 
(*------------------------------------------------------------------*)
(** {2 Automated reasoning} *)

(** [get_trs s] returns a term rewriting system that corresponds to the set of
    equalities between messages. It can be used to check if an equality is
    implied by the set of messages hypotheses. 
    May timeout. *)
val get_trs : sequent -> Completion.state Utils.timeout_r

(** [get_models s] returns a set of minimal models corresponding to the 
    trace atoms in the sequent [s]. 
    See module [Constr]. 
    May timeout. *)
val get_models : sequent -> Constr.models Utils.timeout_r

(** See [Constr.query] *)
val query : precise:bool -> t -> Constr.trace_literal list -> bool

val query_happens : precise:bool -> t -> Term.timestamp -> bool

(** If [message_atoms_valid s] returns [true] then (dis)equalities over
  * terms on both sides of the sequents make the sequent valid. 
  * May timeout. *)
val eq_atoms_valid : sequent -> bool Utils.timeout_r

(** [constraints_valid s] returns true if constraints make the sequent valid,
  * taking into account constraint trace formula hypotheses and atomic
  * constraint conclusion. 
  * May timeout. *)
val constraints_valid : sequent -> bool Utils.timeout_r

(** [get_ts_equalities s] returns all the equalities between timestamps
    derivable from its hypothesis. 
    May timeout. *)
val get_ts_equalities :
  precise:bool -> sequent -> Term.timestamp list list Utils.timeout_r

(** [get_ind_equalities s] returns all the equalities between indices
    derivable from its hypothesis. 
    May timeout. *)
val get_ind_equalities :
  precise:bool -> sequent -> Vars.index list list Utils.timeout_r

(** [maximal_elems s ts] returns the maximal elements of the timestamps,
    according to their ordering derived from the hypothesis in [s]. 
    May timeout. *)
val maximal_elems : 
  precise:bool -> sequent -> Term.timestamp list -> 
  Term.timestamp list Utils.timeout_r


(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** [subst subst s] returns the sequent [s] where the substitution has
    been applied to all hypotheses and the goal.
    It removes trivial equalities (e.g x=x). *)
val subst : Term.subst -> sequent -> sequent

(** [get_all_terms s] returns all the messages appearing at toplevel
  * in [s]. *)
val get_all_messages : sequent -> Term.message list

