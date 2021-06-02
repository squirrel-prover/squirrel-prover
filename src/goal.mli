module L = Location
module SE = SystemExpr

module TS = LowTraceSequent
module ES = LowEquivSequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
type t = Trace of TS.t | Equiv of ES.t

val pp : Format.formatter -> t -> unit
val pp_init : Format.formatter -> t -> unit

val get_env : t -> Vars.env

(*------------------------------------------------------------------*)
type named_goal = string * t

(*------------------------------------------------------------------*)
type ('a,'b) lemma_g = { 
  gc_name   : 'a; 
  gc_tyvars : Type.tvars;
  gc_system : SE.system_expr;
  gc_concl  : 'b;
}

(*------------------------------------------------------------------*)
type       lemma = (string,  Equiv.gform) lemma_g
type equiv_lemma = (string,   Equiv.form) lemma_g
type reach_lemma = (string, Term.message) lemma_g

type lemmas = lemma list


(*------------------------------------------------------------------*)
type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

type       hyp_or_lemma = (ghyp,   Equiv.gform) lemma_g
type equiv_hyp_or_lemma = (ghyp,   Equiv.form) lemma_g
type reach_hyp_or_lemma = (ghyp, Term.message) lemma_g

(*------------------------------------------------------------------*)
val is_reach_lemma : ('a, Equiv.gform) lemma_g -> bool
val is_equiv_lemma : ('a, Equiv.gform) lemma_g -> bool

val to_reach_lemma : 
  ?loc:L.t -> ('a, Equiv.gform) lemma_g -> ('a, Term.message) lemma_g
val to_equiv_lemma : 
  ?loc:L.t -> ('a, Equiv.gform) lemma_g -> ('a, Equiv.form)   lemma_g

(*------------------------------------------------------------------*)
(** {2 Type of parsed goals} *)

type p_goal_form =
  | P_trace_goal of Decl.p_goal_reach_cnt

  | P_equiv_goal of SE.p_system_expr * Theory.bnds * Theory.equiv_form L.located

  | P_equiv_goal_process of SE.p_system_expr

type p_goal = Decl.p_goal_name * p_goal_form

(*------------------------------------------------------------------*)
(** {2 Convert equivalence formulas and goals} *)

val make_equiv_goal :
  table:Symbols.table ->
  hint_db:Hint.hint_db ->
  string ->
  SE.system_expr -> Theory.bnds -> Theory.equiv_form L.located -> lemma * t

val make_trace_goal :
  tbl:Symbols.table -> 
  hint_db:Hint.hint_db ->
  string -> Decl.p_goal_reach_cnt -> lemma * t

(** Create observational equivalence goal for the given biprocess. *)
val make_equiv_goal_process :
  table:Symbols.table -> 
  hint_db:Hint.hint_db ->
  string -> SE.system_expr -> lemma * t
