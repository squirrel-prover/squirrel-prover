open Utils

module Args = TacticsArgs
module Pos  = Match.Pos
module Sv   = Vars.Sv

(*------------------------------------------------------------------*)
include LowRewrite

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** as an instance been found:
    - [pat]: pattern of the instance found (no free variables left)
    - [right]: right term instantiated with the instance found
    - [system]: systems applying to the instance found *) 
type found = { 
  pat    : Term.term Term.pat; 
  right  : Term.term;
  system : SE.t; 
  subgs  : (SE.t * Term.term) list;
}

type rw_state = { 
  rl_system  : SE.t;
  init_pat   : Term.term Term.pat;
  init_subs  : Term.term list;
  init_right : Term.term;

  found_instance : [ `False | `Found of found ];
}

(*------------------------------------------------------------------*)
(** Rewrite error *)
type error = 
  | NothingToRewrite
  | MaxNestedRewriting
  | RuleBadSystems of string

(*------------------------------------------------------------------*)
(** Recast a rewrite error as a [Tactic] error *)
let recast_error ~loc = function
  | NothingToRewrite -> soft_failure ~loc Tactics.NothingToRewrite

  | MaxNestedRewriting ->
    hard_failure ~loc (Failure "max nested rewriting reached (1000)")

  | RuleBadSystems s ->
    soft_failure ~loc (Tactics.Failure ("rule bad systems: " ^ s))

(*------------------------------------------------------------------*)
(** Not exported *)
exception Failed of error

(*------------------------------------------------------------------*)
(** Build the rewrite state corresponding to a rewrite rule.

    - [systems] are the systems applying to the term we are rewriting in

    Tries to rename the projections of [rule] in a way which is 
    compatible with [systems]. 
    Raise [Failed `RuleBadSystems] if it failed  *)
let mk_state
    (rule : rw_rule)
    (systems : (Term.proj * System.Single.t) list option) 
  : rw_state
  = 
  let left, right = rule.rw_rw in

  (* substitution renaming the projections of [rule] using corresponding 
     projections of systems, if any. *)
  let psubst : (Term.proj * Term.proj) list option = 
    match systems with
    | None -> None
    | Some systems ->
      if not (SE.is_fset rule.rw_system) then
        (* [rule] applies to all systems in [systems], nothing to do *)
        let () = assert (SE.is_any_or_any_comp rule.rw_system) in
        None

      else begin
        (* [rule] may not apply to all systems in [systems] *)
        let rule_systems = SE.to_list (SE.to_fset rule.rw_system) in
        if systems = rule_systems then None else
          (* [l] contains tuples [(p,q), single] where:
             - [p] is a projection of [rule.rw_system] for [single]
             - [q] is a projection of [systems] for [single] *)
          let l =
            List.filter_map (fun (p, single) ->
                List.find_map (fun (p_rule, rule_single) -> 
                    if single = rule_single then
                      Some ((p_rule,p), single)
                    else None
                  ) rule_systems
              ) systems
          in

          (* If two projections of [rule.rw_system] applies to the
             same element in [systems], there is an ambiguity
             about which rewriting to apply.
             In that case, we raise an error. *)
          if List.exists (fun ((p_rule, p), single) ->
              List.exists (fun ((p_rule', p'), single') ->
                  p_rule <> p_rule' && p = p' && single = single'
                ) l
            ) l then
            raise (Failed (RuleBadSystems "system projection ambiguity"));

          Some (List.map fst l)
      end
  in

  let projs = omap (List.map snd) psubst in
  let psubst = odflt [] psubst in

  if projs = Some [] then
    raise (Failed (RuleBadSystems "no system of the rule applies"));

  (* check that all projection of [rule] on [projs] are valid *)
  let () = match projs with
    | None -> ()
    | Some projs ->
      let left  = Term.subst_projs psubst left in
      let right = Term.subst_projs psubst right in
      List.iter (fun proj ->
          let left = Term.project1 proj left in
          let right = Term.project1 proj right in
          check_rule { rule with rw_rw = left, right }
        ) projs
  in

  let mk_form f =
    Term.project_opt projs (Term.subst_projs psubst f)
  in
  { rl_system = rule.rw_system;
    init_pat = Term.{ 
        pat_tyvars = rule.rw_tyvars; 
        pat_vars   = rule.rw_vars; 
        pat_term   = mk_form left;
      };
    init_right     = mk_form right;
    init_subs      = List.map mk_form rule.rw_conds;
    found_instance = `False; } 


(*------------------------------------------------------------------*)
(* If there is a match (with [mv]), substitute [occ] by [right] where
   free variables are instantiated according to [mv], and variables
   bound above the matched occurrences are universally quantified in
   the generated sub-goals. *)
let rw_inst
    (expand_context : Macros.expand_context)
    (table : Symbols.table) (hyps : Hyps.TraceHyps.hyps Lazy.t) 
  : rw_state Pos.f_map_fold 
  = 
  let doit
      (occ : Term.term)
      (se : SE.t) (vars : Vars.vars) (conds : Term.terms) _p
      (s : rw_state) 
    =
    let hyps =                 (* adds [conds] in [hyps] *)
      Lazy.map (fun hyps ->
          List.fold_left (fun hyps cond ->
              Hyps.TraceHyps.add AnyName (`Reach cond) hyps
            ) hyps conds
        ) hyps
    in

    let projs : Term.projs option = 
      if SE.is_fset se then Some (SE.to_projs (SE.to_fset se)) else None
    in

    if not (SE.subset table se s.rl_system) then 
      s, `Continue
    else 
      match s.found_instance with
      | `Found inst -> 
        (* we already found the rewrite instance earlier *)

        (* check if the same system apply to the subterm *)
        if not (SE.subset table se inst.system) then 
          s, `Continue 
        else
          let context = SE.reachability_context se in
          begin
            match 
              Match.T.try_match ~expand_context ~hyps table context occ inst.pat 
            with
            | NoMatch _ | FreeTyv -> s, `Continue
            | Match mv -> 
              (* project the already found instance with the projections
                 applying to the current subterm *)
              s, `Map (Term.project_opt projs inst.right)
          end

      | `False ->
        (* project the pattern *)
        let pat_proj = Term.project_tpat_opt projs s.init_pat in

        let context = SE.reachability_context se in
        match 
          Match.T.try_match ~expand_context ~hyps table context occ pat_proj 
        with
        | NoMatch _ | FreeTyv -> s, `Continue

        (* head matches *)
        | Match mv -> 
          (* we found the rewrite instance *)
          let subst = Match.Mvar.to_subst ~mode:`Match mv in
          let left = Term.subst subst pat_proj.pat_term in
          let right = 
            let right_proj = Term.project_opt projs s.init_right in
            Term.subst subst right_proj
          in
          let found_subs =
            List.map (fun rsub ->
                let rsub = Term.project_opt projs rsub in
                se, 
                Term.mk_forall ~simpl:true vars (Term.mk_impls ~simpl:true conds (Term.subst subst rsub))
              ) s.init_subs
          in

          let found_pat = Term.{ 
              pat_term   = left;
              pat_tyvars = [];
              pat_vars   = Sv.empty; 
            } in

          let found_instance = `Found {
              pat    = found_pat;
              right;
              system = se;
              subgs  = found_subs;
            } in

          { s with found_instance }, `Map right
  in
  doit

(*------------------------------------------------------------------*)
(** {2 Rewrite at head position} *)

let rewrite_head
    (table : Symbols.table)
    (expand_context : Macros.expand_context)
    (hyps  : Hyps.TraceHyps.hyps Lazy.t)
    (sexpr : SE.t)
    (rule  : rw_rule)
    (t     : Term.term) : (Term.term * (SE.arbitrary * Term.term) list) option
  =
  let systems = SE.to_list_any sexpr in
  let s = mk_state rule systems in
  match rw_inst expand_context table hyps t sexpr [] [] Pos.root s with
  | _, `Continue -> None
  | { found_instance = `Found inst }, `Map t -> Some (t, inst.subgs)
  | _ -> assert false

(*------------------------------------------------------------------*)
(** {2 Whole-term rewriting} *)

type rw_res = Equiv.any_form * (SE.context * Term.term) list

type rw_res_opt = 
  | RW_Result of rw_res
  | RW_Failed of error

(*------------------------------------------------------------------*)
let rewrite
    (table  : Symbols.table)
    (system : SE.context)
    (expand_context : Macros.expand_context)
    (env    : Vars.env)
    (hyps   : Hyps.TraceHyps.hyps)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res_opt
  =
  let check_max_rewriting : unit -> unit =
    let cpt_occ = ref 0 in
    fun () ->
      if !cpt_occ > 1000 then   (* hard-coded *)
        raise (Failed MaxNestedRewriting);
      incr cpt_occ;
  in

  (* Build the rewrite state corresponding to the rewrite rule [rule] and the 
     systems applying to [target].
     This may require renaming projections in [rule], and removing some
     projections from [rule]. *)
  let s = 
    let target_systems =
      match target with
      | `Equiv _ -> Some (SE.to_list (oget system.pair))
      | `Reach _ -> SE.to_list_any system.set
    in
    mk_state rule target_systems
  in

  let hyps = lazy hyps in

  (* Attempt to find an instance of [left], and rewrites all occurrences of
     this instance.
     Return: (f, subs) *)
  let rec _rewrite (mult : Args.rw_count) (f : Equiv.any_form) 
    : Equiv.any_form * (SE.t * Term.term) list
    =
    check_max_rewriting ();

    let s, f = match f with
      | `Equiv f ->
        let s, _, f = 
          Pos.map_fold_e (rw_inst expand_context table hyps) env system s f 
        in
        s, `Equiv f

      | `Reach f ->
        let s, _, f = 
          Pos.map_fold (rw_inst expand_context table hyps) env system.set s f 
        in
        s, `Reach f
    in

    match mult, s.found_instance with
    | `Any, `False -> f, []

    | (`Once | `Many), `False -> raise (Failed NothingToRewrite)

    | (`Many | `Any), `Found inst  ->
      let f, rsubs' = _rewrite `Any f in
      f, List.rev_append inst.subgs rsubs'

    | `Once, `Found inst -> f, inst.subgs
  in

  match _rewrite mult target with
  | f, subs            -> 
    let subs = List.rev_map (fun (se, t) -> { system with set = se; }, t) subs in
    RW_Result (f, subs)
  | exception Failed e -> RW_Failed e

let rewrite_exn   
    ~(loc   : L.t)
    (table  : Symbols.table)
    (system : SE.context)
    (expand_context : Macros.expand_context)
    (env    : Vars.env)
    (hyps   : Hyps.TraceHyps.hyps)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res
  =
  match rewrite table system expand_context env hyps mult rule target with
  | RW_Result r -> r
  | RW_Failed e -> recast_error ~loc e

(*------------------------------------------------------------------*)
(** {2 Higher-level rewrite} *)

let high_rewrite
    ~(mode   : [`TopDown of bool | `BottomUp])
    (table   : Symbols.table)
    (system  : SE.t)
    (venv    : Vars.env)         (* for clean variable naming *)
    (mk_rule : Vars.vars -> Pos.pos -> rw_rule option) 
    (t       : Term.term)
  : Term.term 
  =
  let hyps = lazy Hyps.TraceHyps.empty in

  let rw_inst : Pos.f_map = 
    fun occ se vars conds p ->
      (* build the rule to apply at position [p] using mk_rule *)
      match mk_rule vars p with
      | None -> `Continue
      | Some rule ->
        assert (rule.rw_conds = []);

        let state = mk_state rule (SE.to_list_any se) in
        snd (rw_inst InSequent table hyps occ se vars conds p state)
  in

  let _, f = Pos.map ~mode rw_inst venv system t in
  f
