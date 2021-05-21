open Utils
    
module L = Location

module TS = LowTraceSequent
module ES = LowEquivSequent

module SE = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {2 Goals} *)

type t = Trace of TS.t | Equiv of ES.t

let get_env = function
  | Trace j -> TS.env j
  | Equiv j -> ES.env j

let get_table = function
  | Trace j -> TS.table j
  | Equiv j -> ES.table j

let pp ch = function
  | Trace j -> TS.pp ch j
  | Equiv j -> ES.pp ch j

let pp_init ch = function
  | Trace j -> Term.pp ch (TS.goal j)
  | Equiv j -> ES.pp_init ch j

(*------------------------------------------------------------------*)

(** An open named goal *)
type named_goal = string * t

type named_goals = named_goal list

(*------------------------------------------------------------------*)
type ('a,'b) lemma_g = { 
  gc_name   : 'a; 
  gc_tyvars : Type.tvars;
  gc_system : SE.system_expr;
  gc_concl  : 'b;
}

(*------------------------------------------------------------------*)
type gform = [`Equiv of Equiv.form | `Reach of Term.message]

type       lemma = (string,        gform) lemma_g
type equiv_lemma = (string,   Equiv.form) lemma_g
type reach_lemma = (string, Term.message) lemma_g

type lemmas = lemma list


(*------------------------------------------------------------------*)
type ghyp = [ `Hyp of Ident.t | `Lemma of string ]

type       hyp_or_lemma = (ghyp,        gform) lemma_g
type equiv_hyp_or_lemma = (ghyp,   Equiv.form) lemma_g
type reach_hyp_or_lemma = (ghyp, Term.message) lemma_g

(*------------------------------------------------------------------*)
let mk_goal_concl gc_name gc_system gc_tyvars gc_concl =
  { gc_name; gc_system; gc_tyvars; gc_concl }

let is_reach_lemma gconcl : bool =
  match gconcl.gc_concl with
  | `Equiv _ -> false
  | `Reach _ -> true    

let is_equiv_lemma gconcl : bool =
  match gconcl.gc_concl with
  | `Equiv _ -> true
  | `Reach _ -> false    

let to_reach_lemma ?loc gconcl = 
  match gconcl.gc_concl with
  | `Reach f -> { gconcl with gc_concl = f }

  | `Equiv _ -> 
    Tactics.soft_failure ?loc (Failure "expected a reachability formula")

let to_equiv_lemma ?loc gconcl = 
  match gconcl.gc_concl with
  | `Equiv f -> { gconcl with gc_concl = f }

  | `Reach _ -> 
    Tactics.soft_failure ?loc (Failure "expected an equivalence formula")

(*------------------------------------------------------------------*)
(** {2 Parsed goals} *)

type p_equiv = Theory.term list 

type p_equiv_form = 
  | PEquiv of p_equiv
  | PReach of Theory.formula
  | PImpl of p_equiv_form * p_equiv_form

type p_goal_form =
  | P_trace_goal of Decl.p_goal_reach_cnt

  | P_equiv_goal of SE.p_system_expr * Theory.bnds * p_equiv_form L.located

  | P_equiv_goal_process of SE.p_system_expr

type p_goal = Decl.p_goal_name * p_goal_form

(*------------------------------------------------------------------*)
(** {2 Convert equivalence formulas and goals} *)

let convert_el cenv ty_vars (env : Vars.env) el : Term.message =   
  let t, _ = Theory.convert_i cenv ty_vars env el in
  t  

let convert_equiv cenv ty_vars (env : Vars.env) (e : p_equiv) =
  List.map (convert_el cenv ty_vars env) e

let convert_equiv_form cenv ty_vars env (p : p_equiv_form) =
  let rec conve p =
    match p with
    | PImpl (f,f0) -> 
      Equiv.Impl (conve f, conve f0)
    | PEquiv e -> 
      Equiv.Atom (Equiv.Equiv (convert_equiv cenv ty_vars env e))
    | PReach f -> 
      Equiv.Atom (Equiv.Reach (Theory.convert cenv ty_vars env f Type.Boolean))
  in

  conve p

let make_trace_goal ~tbl ~hint_db gname (pg : Decl.p_goal_reach_cnt) 
  : lemma * t =
  let system = SE.parse_se tbl pg.g_system in

  let ty_vars = List.map (fun ls -> Type.mk_tvar (L.unloc ls)) pg.g_tyvars in  

  let conv_env = Theory.{ table = tbl; cntxt = InGoal; } in

  let env, evs = Theory.convert_p_bnds tbl ty_vars Vars.empty_env pg.g_vars in

  let g = Theory.convert conv_env ty_vars env pg.g_form Type.Boolean in

  let s = TS.init ~system ~table:tbl ~hint_db ~ty_vars ~env ~goal:g in

  let gc = 
    mk_goal_concl gname system ty_vars (`Reach (Term.mk_forall evs g)) 
  in
  
  (* final proved formula, current sequent *)
  gc, Trace s

let make_equiv_goal ~table ~hint_db
    gname se (bnds : Theory.bnds) (p_form : p_equiv_form L.located) : lemma * t =
  let env, evs = Theory.convert_p_bnds table [] Vars.empty_env bnds in

  let conv_env = Theory.{ table = table; cntxt = InGoal; } in

  let f = convert_equiv_form conv_env [] env (L.unloc p_form) in

  let gc = mk_goal_concl gname se [] (`Equiv (Equiv.mk_forall evs f)) in
  
  gc, Equiv (ES.init se table hint_db env ES.H.empty f)


let make_equiv_goal_process ~table ~hint_db gname system : lemma * t =
  let env, ts = Vars.make `Approx Vars.empty_env Type.Timestamp "t" in
  let term = Term.Macro (Term.frame_macro,[],Term.Var ts) in
  let goal = Equiv.(Atom (Equiv [term])) in

  let happens = Term.Atom (`Happens (Term.Var ts)) in
  let hyp = Equiv.Atom (Reach happens) in

  let hyps = ES.H.empty in
  let id = ES.H.fresh_id "H" hyps in
  let _, hyps = ES.H.add ~force:false id hyp hyps in

  let gc = 
    mk_goal_concl gname system [] (`Equiv (Equiv.mk_forall [Vars.EVar ts] goal)) 
  in
  
  ( gc, Equiv (ES.init system table hint_db env hyps goal) )
