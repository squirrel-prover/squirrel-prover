(** This module implement sequents used to prove trace properties.
    A sequent is made of:
    - a set of hypotheses, that can be generic formulas, trace formulas or
   (dis)equalities between messages;
    - a conclusion formula;
    - an environment to store all the variables appearing inside the formulas.
*)

open Term

module Args = TacticsArgs
  
(** {2 Sequent type and basic operations} *)

type t
type sequent = t

val pp : Format.formatter -> sequent -> unit

(** [init formula table] returns a sequent with an empty set of hypotheses, and 
    the given formula as conclusion. *)
val init : 
  system:SystemExpr.system_expr -> Symbols.table -> formula -> sequent
  
(** Get the system which the sequent is reasoning about. *)
val system : sequent -> SystemExpr.system_expr

(** Get the symbol table of the sequent. *)
val table : sequent -> Symbols.table

(** Change the system of a sequent. *)
val set_system : SystemExpr.system_expr -> sequent -> sequent

(** Change the table of a sequent. *)
val set_table : Symbols.table -> sequent -> sequent

(** Project diff-operators occurring in a sequent;
  * only makes sense when a sequent for a bi-system has just
  * been narrowed to a projected system. *)
val pi : Term.projection -> sequent -> sequent

(** [set_env e s] returns a new sequent with
  * the environment set to [e]. *)
val set_env : Vars.env -> sequent -> sequent

(** [env s] returns the environment of the sequent. *)
val env : sequent -> Vars.env

(** [set_conclusion f s] set the conclusion formula of the sequent to [f]. *)
val set_conclusion : formula -> sequent -> sequent

(** [conclusion s] returns the conclusion formula of the sequent. *)
val conclusion : sequent -> formula


(*------------------------------------------------------------------*)
(** {2 Hypotheses} *)

(** Hypothesis *)
type hyp = Term.formula

(** Local declaration *)
type ldecl = Ident.t * hyp

val pp_hyp   : Format.formatter -> hyp   -> unit
val pp_ldecl : ?dbg:bool -> Format.formatter -> ldecl -> unit  
             
module Hyps : sig  
  (** [add id f s] returns the sequent [s] with [f] added to its hypotheses. 
      The new sequent will be automatically enriched with equalities 
      expressing relevant macro definitions, as well as conditions of all 
      named actions that are assumed to happen. *)
  val add : Args.naming_pat -> formula -> sequent -> sequent

  (** Same as [add], but also returns the ident of the added hypothesis. *)
  val add_i : Args.naming_pat -> formula -> sequent -> Ident.t * sequent

  val add_list :
    (Args.naming_pat * formula) list -> sequent -> sequent

  val add_i_list :
    (Args.naming_pat * formula) list -> sequent -> Ident.t list * sequent
                                                          
  (*------------------------------------------------------------------*)
  (** [is_hyp f s] returns true if the formula appears inside the hypotesis
      of the sequent [s].  *)
  val is_hyp : formula -> sequent -> bool

  (** [by_id id s] returns the hypothesis with id [id] in [s]. *)
  val by_id : Ident.t -> sequent -> formula

  (** Same as [by_id], but does a look-up by name and returns the full local 
      declaration. *)
  val by_name : string -> sequent -> ldecl

  (** [mem_id id s] returns true if there is an hypothesis with id [id] 
      in [s]. *)
  val mem_id : Ident.t -> sequent -> bool

  (** Same as [mem_id], but does a look-up by name. *)  
  val mem_name : string -> sequent -> bool

  (** Find the first local declaration satisfying a predicate. *)
  val find_opt : (Ident.t -> formula -> bool) -> sequent -> ldecl option

  (** Exceptionless *)
  val find_map : (Ident.t -> hyp -> 'a option) -> sequent -> 'a option

  (** Find if there exists a local declaration satisfying a predicate. *)
  val exists : (Ident.t -> formula -> bool) -> sequent -> bool

  (** Removes a formula. *)
  val remove : Ident.t -> sequent -> sequent

  val fold : (Ident.t -> formula -> 'a -> 'a) -> sequent -> 'a -> 'a

  val pp : Format.formatter -> sequent -> unit
    
  val pp_dbg : Format.formatter -> sequent -> unit
end


(** [subst subst s] returns the sequent [s] where the substitution has
    been applied to all hypotheses and the conclusion.
    It removes trivial equalities (e.g x=x). *)
val subst : Term.subst -> sequent -> sequent
  
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
val query : t -> Constr.trace_literal list -> bool

val query_happens : t -> Term.timestamp -> bool

(** If [message_atoms_valid s] returns [true] then (dis)equalities over
  * messages on both sides of the sequents make the sequent valid. 
  * May timeout. *)
val message_atoms_valid : sequent -> bool Utils.timeout_r

(** [constraints_valid s] returns true if constraints make the sequent valid,
  * taking into account constraint trace formula hypotheses and atomic
  * constraint conclusion. 
  * May timeout. *)
val constraints_valid : sequent -> bool Utils.timeout_r

(** [get_ts_equalities s] returns all the equalities between timestamps
    derivable from its hypothesis. 
    May timeout. *)
val get_ts_equalities : sequent -> Term.timestamp list list Utils.timeout_r

(** [get_ind_equalities s] returns all the equalities between indices
    derivable from its hypothesis. 
    May timeout. *)
val get_ind_equalities : sequent -> Vars.index list list Utils.timeout_r

(** [maximal_elems s ts] returns the maximal elements of the timestamps,
    according to their ordering derived from the hypothesis in [s]. 
    May timeout. *)
val maximal_elems : sequent -> Term.timestamp list ->
  Term.timestamp list Utils.timeout_r


(*------------------------------------------------------------------*)
(** {2 Misc} *)

(** [get_all_terms s] returns all the term appearing at toplevel
  * in message hypotheses of [s]. *)
val get_all_terms : sequent -> Term.message list

