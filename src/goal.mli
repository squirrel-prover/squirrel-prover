module L = Location
module SE = SystemExpr

type lsymb = Theory.lsymb

type t = Trace of TraceSequent.t | Equiv of EquivSequent.t

(** A goal of the prover is simply a name and a formula *)
type named_goal = string * t

(** A goal conclusion *)
type goal_concl = { 
  gc_name   : string; 
  gc_tyvars : Type.tvars;
  gc_system : SE.system_expr;
  gc_concl  : [`Equiv of Equiv.form | `Reach of Term.message];
}

type goal_concls = goal_concl list

val pp : Format.formatter -> t -> unit
val pp_init : Format.formatter -> t -> unit

val get_env : t -> Vars.env

val is_reach_gconcl : goal_concl -> bool
val is_equiv_gconcl : goal_concl -> bool

(*------------------------------------------------------------------*)
(** {2 Type of parsed goals} *)

type p_equiv = Theory.term list 

type p_equiv_form = 
  | PEquiv of p_equiv
  | PReach of Theory.formula
  | PImpl  of p_equiv_form * p_equiv_form

type p_goal_form =
  | P_trace_goal of Decl.p_goal_reach_cnt

  | P_equiv_goal of SE.p_system_expr * Theory.bnds * p_equiv_form L.located

  | P_equiv_goal_process of SE.p_system_expr

type p_goal = Decl.p_goal_name * p_goal_form

(*------------------------------------------------------------------*)
(** {2 Convert equivalence formulas and goals} *)

val make_equiv_goal :
  table:Symbols.table ->
  string ->
  SE.system_expr -> Theory.bnds -> p_equiv_form L.located -> goal_concl * t

val make_trace_goal :
  tbl:Symbols.table -> string -> Decl.p_goal_reach_cnt -> goal_concl * t

val make_equiv_goal_process :
  table:Symbols.table -> string -> SE.system_expr -> goal_concl * t
