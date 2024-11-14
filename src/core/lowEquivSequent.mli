(** Equivalence sequents,
    or more accurately global sequents whose conclusion
    is a global meta-formula. *)

open Ppenv

module SE = SystemExpr

(*------------------------------------------------------------------*)
include LowSequent.S with
          type  hyp_form = Equiv.global_form and
          type conc_form = Equiv.global_form

(*------------------------------------------------------------------*)
(** {2 Creation of global sequents} *)

(** Initialize a sequent with the given components.
    At most one hypothesis can be given, which will be named "H":
    this is intended to ease simple cases like observational
    equivalence goals.
    For more general cases, the global meta-formula used as conclusion
    can include implications. *)
val init : ?no_sanity_check:bool -> env:Env.t-> ?hyp:Equiv.form -> Equiv.form -> t

(** Special pretty-printer for initial sequents.
    It does not display hypotheses, which might be misleading. *)
val pp_init : t formatter_p

(** Free variables + var env **toplevel** sanity check *)
val sanity_check : t -> unit

(*------------------------------------------------------------------*)
(** {2 Misc} *)

val get_system_pair : t -> SE.pair
val get_system_pair_projs : t -> Projection.t * Projection.t

(*------------------------------------------------------------------*)
(** {2 Utilities for equivalence sequents}
    Equivalence sequents are global sequents whose conclusion
    is an equivalence atom. *)

val set_equiv_conclusion : Equiv.equiv -> t -> t

(** Get one of the projections of the biframe,
    as a list of terms where diff operators have been fully
    eliminated.
    @return [None] if the conclusion is not an equivalence atom. *)
val get_frame : Projection.t -> t -> Equiv.equiv option

val conclusion_is_equiv : t -> bool

val conclusion_as_equiv : t -> Equiv.equiv

(*------------------------------------------------------------------*)
(** {2 Trace sequents and reachability goals} *)

(** Change sequent conclusion to some reachability atom. *)
val set_reach_conclusion : Term.term -> t -> t

(** Convert a global sequent whose conclusion is a reachability
    atom to a trace sequent.
    @raise Tactics.soft_failure if sequent conclusion is not well-formed. *)
val to_trace_sequent : t -> LowTraceSequent.t

(*------------------------------------------------------------------*)
(** {2 Deducibility and non-deducibility goals} 

    Goals corresponding to the predicates [u |> v] and [u *> v].
    Defined in [WeakSecrecy.sp]. *)

(** There are two kinds of secrecy judgements:
    deduction  [( |> )] and non-deduction [( *> )] *)
type secrecy_kind = Deduce | NotDeduce

(** The type of a secrecy goal. It's actually the 
    global formula, but it's intentionally left abstract. *)
type secrecy_goal

(** Checks whether a global formula is a secrecy judgement. 
    This in particular implies that [WeakSecrecy] is loaded. *)
val is_secrecy : Symbols.table -> Equiv.form -> bool

(** Constructs a secrecy goal. The lists of types and of terms
 are the left side of the goal and must have the same length. 
 The [WeakSecrecy] module must be loaded. *)
val mk_secrecy_goal : 
  Symbols.table -> secrecy_kind -> SE.fset -> 
  Type.ty list -> Type.ty -> Term.terms -> Term.term -> secrecy_goal

(** Constructs a secrecy goal from a global formula. 
 *Assumes [is_secrecy] holds*. *)
val mk_secrecy_goal_from_form : Symbols.table -> Equiv.form -> secrecy_goal 

(** Constructs the global formula for a secrecy goal. *)
val mk_form_from_secrecy_goal : secrecy_goal -> Equiv.form

(** Extracts the kind of secrecy goal. *)
val secrecy_kind : secrecy_goal -> secrecy_kind

(** Returns the system of the secrecy goal *)
val secrecy_system : secrecy_goal -> SE.t

(** Returns the left-hand side of the secrecy goal. 
    In case it is a tuple, or nested tuples, flattens it as
    a list of terms. *)
val secrecy_left : secrecy_goal -> Term.terms

(** Returns the right-hand side of the secrecy goal. *)
val secrecy_right : secrecy_goal -> Term.term

(** Checks whether the sequent's conclusion is a secrecy judgement
    (necessarily, this implies that WeakSecrecy is loaded) *)
val conclusion_is_secrecy : t -> bool

(** Extracts the secrecy goal from a sequent. 
    Fails if the sequent is not a secrecy sequent. *)
val conclusion_as_secrecy : t -> secrecy_goal

(** Returns a new secrecy goal where the left-hand side has been updated*)
val secrecy_update_left : Term.terms -> secrecy_goal -> secrecy_goal

(** Returns a new secrecy goal where the right-hand side has been updated*)
val secrecy_update_right : Term.terms -> secrecy_goal -> secrecy_goal

(*------------------------------------------------------------------*)
(** {2 Automated reasoning} *)

val query_happens : precise:bool -> t -> Term.term -> bool

(** Utility *)

(* Constructs the trace context for the pair of systems. *)
val mk_pair_trace_cntxt : sequent -> Constr.trace_cntxt

(* Fails if the goal is not an equivalence. *)
val check_conclusion_is_equiv : sequent -> unit
