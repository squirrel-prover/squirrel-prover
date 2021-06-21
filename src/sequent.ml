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

  val get_k_hyp_or_lemma : 
    'a Equiv.f_kind -> Theory.lsymb -> t -> (Goal.ghyp, 'a) Goal.lemma_g

  val reduce : Reduction.red_param -> t -> 'a Equiv.f_kind -> 'a -> 'a

  val convert_pt_hol : 
    Theory.p_pt_hol -> 'a Equiv.f_kind -> t -> Goal.ghyp * 'a Match.pat
end

module Mk (S : LowSequent.S) : S with
  type t = S.t                   and
  type conc_form = S.conc_form   and
  type hyp_form = S.hyp_form     =
struct
  include S

  let is_hyp_or_lemma (name : lsymb) (s : S.t) =
    Hyps.mem_name (L.unloc name) s || Prover.is_lemma (L.unloc name)

  let is_equiv_hyp_or_lemma (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s || Prover.is_equiv_lemma (L.unloc name)

  let is_reach_hyp_or_lemma (name : lsymb) (s : sequent) =
    Hyps.mem_name (L.unloc name) s || Prover.is_reach_lemma (L.unloc name)

  let get_k_hyp_or_lemma
    : type a. a Equiv.f_kind -> lsymb -> t -> (Goal.ghyp, a) Goal.lemma_g
    = fun k name s ->

      if Hyps.mem_name (L.unloc name) s then
        let id, f = Hyps.by_name name s in
        Goal.{ gc_name = `Hyp id;
               gc_system = system s;
               gc_tyvars = [];
               gc_concl =
                 Equiv.Babel.convert
                   ~loc:(L.loc name)
                   ~src:S.hyp_kind
                   ~dst:k
                   f }
      else
        let lem = Prover.get_lemma name in
        (* Verify that it applies to the current system. *)
        if not (SE.systems_compatible (S.system s) lem.gc_system) then
          Tactics.hard_failure Tactics.NoAssumpSystem;
        { Goal.gc_name = `Lemma lem.Goal.gc_name ;
          gc_system = lem.gc_system ;
          gc_tyvars = lem.gc_tyvars ;
          gc_concl = Equiv.Babel.convert lem.gc_concl
                       ~src:Equiv.Any_t ~dst:k ~loc:(L.loc name) }

  (*------------------------------------------------------------------*)
  let decompose_forall_k : type a. a Equiv.f_kind -> a -> Vars.evars * a =
    fun f_kind f ->
    match f_kind with
    | Equiv.Local_t ->  Term.Smart.decompose_forall f
    | Equiv.Global_t -> Equiv.Smart.decompose_forall f
    | Equiv.Any_t ->
       match f with
         | `Reach f ->
             let vs,f = Term.Smart.decompose_forall f in vs, `Reach f
         | `Equiv f ->
             let vs,f = Equiv.Smart.decompose_forall f in vs, `Equiv f

  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let convert_pt_hol : type a.
    Theory.p_pt_hol -> a Equiv.f_kind -> S.t -> Goal.ghyp * a Match.pat =
    fun pt f_kind s ->

    let lem = get_k_hyp_or_lemma f_kind pt.p_pt_hid s in
    let f_args, f = decompose_forall_k f_kind lem.gc_concl in
    let f_args, subst = Term.erefresh_vars `Global f_args in
    let f = Equiv.Babel.subst f_kind subst f in

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

          Term.ESubst (Term.mk_var f_arg, t)
        ) pt.p_pt_args f_args0
    in

    (* instantiate [f_args0] by [args] *)
    let f = Equiv.Babel.subst f_kind subst f in

    let pat = Match.{ 
        pat_tyvars = lem.gc_tyvars;
        pat_vars = !pat_vars;
        pat_term = f; } 
    in      
    lem.gc_name, pat

  (*------------------------------------------------------------------*)
  module Reduce = Reduction.Mk(S)

  let reduce = Reduce.reduce 
end
