open Utils

module L = Location
module SE = SystemExpr
module LS = LowSequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** {2 Module type for sequents -- after Prover} *)

module type S = sig
  include LowSequent.S

  val is_hyp_or_lemma        : lsymb -> t -> bool
  val is_equiv_hyp_or_lemma  : lsymb -> t -> bool
  val is_reach_hyp_or_lemma  : lsymb -> t -> bool

  val get_hyp_or_lemma       : lsymb -> t -> Goal.hyp_or_lemma
  val get_equiv_hyp_or_lemma : lsymb -> t -> Goal.equiv_hyp_or_lemma
  val get_reach_hyp_or_lemma : lsymb -> t -> Goal.reach_hyp_or_lemma
  val get_k_hyp_or_lemma : 
    'a LowSequent.s_kind -> lsymb -> t -> (Goal.ghyp, 'a) Goal.lemma_g 

  val reduce : t -> form -> form

  val convert_pt_hol : 
    Theory.p_pt_hol -> 'a LowSequent.s_kind -> t -> Goal.ghyp * 'a Term.pat
end

module Mk (S : LowSequent.S) : S with type t = S.t and type form = S.form = struct
  include S

  let is_hyp_or_lemma (name : lsymb) (s : S.t) =
    Hyps.mem_name (L.unloc name) s || Prover.is_lemma (L.unloc name)

  let is_equiv_hyp_or_lemma (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s || Prover.is_equiv_lemma (L.unloc name)

  let is_reach_hyp_or_lemma (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s || Prover.is_reach_lemma (L.unloc name)

  let get_hyp_or_lemma (name : lsymb) (s : sequent) : Goal.hyp_or_lemma =
    let lem =
      if Hyps.mem_name (L.unloc name) s then
        let id, f = Hyps.by_name name s in
        Goal.{ gc_name = `Hyp id;
               gc_system = system s;
               gc_tyvars = [];
               gc_concl = S.gform_of_form f; }
      else
        let lem = Prover.get_lemma name in
        { lem with gc_name = `Lemma lem.Goal.gc_name }
    in

    (* Verify that it applies to the current system. *)
    if not (SE.systems_compatible (S.system s) lem.gc_system) then
      Tactics.hard_failure Tactics.NoAssumpSystem;

    lem

  let get_reach_hyp_or_lemma name s =
    Goal.to_reach_lemma ~loc:(L.loc name) (get_hyp_or_lemma name s)
      
  let get_equiv_hyp_or_lemma name s =
    Goal.to_equiv_lemma ~loc:(L.loc name) (get_hyp_or_lemma name s)

  (*------------------------------------------------------------------*)
  (** [s_kind] variants *)

  let get_k_hyp_or_lemma : type a. 
    a LS.s_kind -> lsymb -> t -> (Goal.ghyp, a) Goal.lemma_g = 
    fun s_kind name s ->
    match s_kind with
    | LowSequent.KEquiv -> get_equiv_hyp_or_lemma name s
    | LowSequent.KReach -> get_reach_hyp_or_lemma name s

  let decompose_forall_k : type a. a LS.s_kind -> a -> Vars.evars * a = 
    fun s_kind f ->
    match s_kind with
    | LowSequent.KReach ->  Term.Smart.decompose_forall f
    | LowSequent.KEquiv -> Equiv.Smart.decompose_forall f

  let subst_k : type a. a LS.s_kind -> Term.subst -> a -> a = 
    fun s_kind subst f ->
    match s_kind with
    | LowSequent.KReach ->  Term.subst subst f
    | LowSequent.KEquiv -> Equiv.subst subst f

  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let convert_pt_hol : type a. 
    Theory.p_pt_hol -> a LowSequent.s_kind -> S.t -> Goal.ghyp * a Term.pat = 
    fun pt s_kind s ->

    let lem = get_k_hyp_or_lemma s_kind pt.p_pt_hid s in
    let f_args, f = decompose_forall_k s_kind lem.gc_concl in
    let f_args, subst = Term.erefresh_vars `Global f_args in
    let f = subst_k s_kind subst f in

    let pt_args_l = List.length pt.p_pt_args in

    if List.length f_args < pt_args_l then
      hard_failure ~loc:(L.loc pt.p_pt_hid) (Failure "too many arguments");

    let f_args0, f_args1 = List.takedrop pt_args_l f_args in

    let cenv = Theory.{ table = S.table s; cntxt = InGoal; } in 
    let pat_vars = ref (Vars.Sv.of_list f_args1) in

    let subst = 
      List.map2 (fun p_arg (Vars.EVar f_arg) ->
          let ty = Vars.ty f_arg in
          let t = 
            Theory.convert ~pat:true cenv (S.ty_vars s) (S.env s) p_arg ty
          in
          let new_p_vs = 
            Vars.Sv.filter (fun (Vars.EVar v) -> Vars.is_pat v) (Term.fv t)
          in
          pat_vars := Vars.Sv.union (!pat_vars) new_p_vs;

          Term.ESubst (Term.Var f_arg, t)
        ) pt.p_pt_args f_args0
    in

    (* instantiate [f_args0] by [args] *)
    let f = subst_k s_kind subst f in

    let pat = Term.{ 
        pat_tyvars = lem.gc_tyvars;
        pat_vars = !pat_vars;
        pat_term = f; } 
    in      
    lem.gc_name, pat

  (*------------------------------------------------------------------*)
  module Reduce = Reduction.Mk(S)

  let reduce s t = Reduce.reduce s t
end
