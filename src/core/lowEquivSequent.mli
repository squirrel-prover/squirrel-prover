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
(** {2 Deducibility and non-deducibility goals} *)
(** Goals corresponding to the predicates "u |> v" and "u *> v".
    Defined in WeakSecrecy.sp. *)

(**An objet of the type [secrecy_goal] represent a goal of
   the form "u |> v" or "u *> v".
   If "u" is a tuple, [left] is a list of each term is the tuple.
   Else, the list [left] contains only one element for "u". *)
type secrecy_goal = {
  predicate : Symbols.predicate;
  left_ty : Type.ty list;
  left : Term.term list;
  right_ty : Type.ty;
  right : Term.term }

(** Requires WeakSecrecy.sp to be loaded.
    [get_secrecy_goal s] returning a [secrecy_goal] representing the goal
    if it is of the form "u |> v" or "u *> v"].
    Returns [None] is the goal is not of the correct form, or if the predicate
    is used in a different system than the sequent's system. *)
val get_secrecy_goal : t -> secrecy_goal option

(** Requires WeakSecrecy.sp to be loaded.
    [mk_secrecy_concl] returning a formula representing [goal]
    in the system of [s].*)
val mk_secrecy_concl : secrecy_goal -> t -> conc_form

(*------------------------------------------------------------------*)
(** {2 Automated reasoning} *)

val query_happens : precise:bool -> t -> Term.term -> bool

(** Utility *)

(* Constructs the trace context for the pair of systems. *)
val mk_pair_trace_cntxt : sequent -> Constr.trace_cntxt

(* Fails if the goal is not an equivalence. *)
val check_conclusion_is_equiv : sequent -> unit
