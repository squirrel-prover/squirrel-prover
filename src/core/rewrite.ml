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
(** An instance been found:
    - [pat]: pattern of the instance found (no free variables left)
    - [right]: right term instantiated with the instance found
    - [system]: systems applying to the instance found 
    - [cond] and [vars]: conditions and variables applying at the subterm 
      where the instance was found.

    Type unification environments has already been closed. *) 
type found = { 
  ienv   : Infer.env;
  pat    : Term.term Term.pat_op; 
  right  : Term.term;
  system : SE.t; 
  conds  : Term.terms;
  vars   : Vars.vars;
  subgs  : Term.term list;      (* [vars] and [conds] not yet added *)
}

(** Build the final subgoals associated to a instance found. *)
let subgoals_of_found (f : found) : (SE.t * Term.term) list =
  List.map (fun subg ->
      let goal =
        Term.mk_forall ~simpl:true f.vars 
          (Term.mk_impls ~simpl:true f.conds subg)
      in 
      f.system, goal
    ) f.subgs

(*------------------------------------------------------------------*)
(** An opened rewrite rule at a given subterm for its corresponding
    system. *)
type open_rw_rule = { 
  system  : SE.t;
  subs  : Term.term list;
  pat   : Term.term Term.pat_op;
  right : Term.term;
  
  ienv : Infer.env;
}

(** Rewrite internal state, propagated downward. *)
type rw_state = [ `False | `Found of found ]

(*------------------------------------------------------------------*)
(** Rewrite error *)
type error = 
  | NothingToRewrite
  | MaxNestedRewriting

(*------------------------------------------------------------------*)
(** Recast a rewrite error as a [Tactic] error *)
let recast_error ~loc = function
  | NothingToRewrite -> soft_failure ~loc Tactics.NothingToRewrite

  | MaxNestedRewriting ->
    hard_failure ~loc (Failure "max nested rewriting reached (1000)")

(*------------------------------------------------------------------*)
(** Not exported *)
exception Failed of error

(*------------------------------------------------------------------*)
exception OpenRuleFailed

let open_failed () = raise OpenRuleFailed
  
(** Open a rewrite rule at a sub-term taken in the system [system].

    Tries to rename the projections of [rule] in a way which is 
    compatible with [system]. 
    Raise [OpenRuleFailed] if it failed  *)
let open_rw_rule table (rule : rw_rule) (system : SE.t) : open_rw_rule = 
  let left, right = rule.rw_rw in

  (* open an inference environment *)
  let ienv = Infer.mk_env () in
  let params, gsubst = Infer.open_params ienv rule.rw_params in

  let rule_system = SE.gsubst gsubst rule.rw_system in

  (* check whether the systems are compatible *)
  let is_compatible =
    if SE.is_var rule_system || SE.is_var system then
      match Infer.unify_se ienv rule_system system with
      | `Ok   -> `Equal
      | `Fail -> open_failed ()
    else if SE.subset_modulo table system rule_system then
      `Subset
    else
      open_failed ()
  in

  let rule_system = Infer.norm_se ienv rule_system in
  let systems     = Infer.norm_se ienv system      in
  
  let mk_form_proj =
    match is_compatible with
    | `Equal -> fun x -> x
    | `Subset -> 
      let projs, psubst = 
        SE.mk_proj_subst ~strict:false ~src:rule_system ~dst:system
      in
      let doit f = Term.project_opt projs (Term.subst_projs psubst f) in
      (* FIXME: svars: remove the [~proj] field of [Term.subst_projs]
         and replace by the code above? *)

      (* check that all projection of [rule] on [projs] are valid *)
      if not (SE.equal0 rule.rw_system systems) then
        check_rule { rule with rw_rw = doit left, doit right };
      
      doit
  in

  (* combine [mk_form_proj] with [gsubst] *)
  let mk_form f = mk_form_proj f |> Term.gsubst gsubst in

  let pat : Term.term Term.pat_op = 
    { 
      pat_op_params = params; 
      pat_op_vars   = 
        List.map (fun (v,tag) -> (Subst.subst_var gsubst v, tag)) rule.rw_vars; 
      pat_op_term   = mk_form left;
    } 
  in
  
  {
    system = rule_system;
    pat;
    right = mk_form right;
    subs  = List.map mk_form rule.rw_conds;
    ienv;
  }

(*------------------------------------------------------------------*)
let hyps_add_conds hyps (conds : Term.terms) =
  List.fold_left (fun hyps cond ->
      Hyps.TraceHyps.add AnyName (LHyp (Local cond)) hyps
    ) hyps conds

(*------------------------------------------------------------------*)
(** If there is a match (with [mv]), substitute [occ] by [right] where
    free variables are instantiated according to [mv], and variables
    bound above the matched occurrences are universally quantified in
    the generated sub-goals. *)
let rw_inst
    (expand_context : Macros.expand_context)
    (table : Symbols.table) (params : Params.t)
    (env : Vars.env) (hyps : Hyps.TraceHyps.hyps) 
    (rule : rw_rule)
  : rw_state Pos.f_map_fold 
  = 
  let doit
      (occ : Term.term)
      (se : SE.t) (vars : Vars.vars) (conds : Term.terms) _p
      (s : rw_state) 
    =
    (* adds [conds] in [hyps] *)
    let hyps = hyps_add_conds hyps conds in

    match s with
    | `Found inst -> 
      (* we already found the rewrite instance earlier *)

      (* check if the same system apply to the subterm *)
      if not (SE.equal table se inst.system) then 
        s, `Continue 
      else
        let ienv = inst.ienv in (* FIXME: why keep using [ienv]? *)
        let context = SE.reachability_context se in
        begin
          match 
            Match.T.try_match
              (* TODO: param: take param as input *)
              ~param:Match.crypto_param
              ~expand_context
              ~ienv ~hyps ~env table context occ inst.pat 
          with
          | NoMatch _ -> s, `Continue
          | Match _mv -> 
            (* When we found another occurrence of the same rewrite
               instance, we clear the conditions that are not shared by 
               both occurrences (i.e. we keep only common conditions) *)
            let conds = List.filter (fun cond -> List.mem cond conds) inst.conds in
            let s = `Found { inst with conds } in

            s, `Map inst.right
        end

    | `False ->
      let context = SE.reachability_context se in

      match
        (* open the rule in the match block, to catch exception below *)
        let op_rule = open_rw_rule table rule se in
        let res_match =
          Match.T.try_match
            (* TODO: param: take param as input *)
            ~param:Match.crypto_param
            ~expand_context ~ienv:op_rule.ienv
            ~hyps ~env table context occ op_rule.pat
        in
        (op_rule, res_match)
      with
      | exception OpenRuleFailed -> s, `Continue (* [open_rw_rule] failed *)

      | _, NoMatch _ -> s, `Continue

      (* head matches *)
      | op_rule, Match mv -> 
        Match.Mvar.check_args_inferred op_rule.pat mv;

        let ienv = op_rule.ienv in
        
        let pat_vars =
          Vars.add_vars op_rule.pat.pat_op_vars env
          (* vars in the pattern are restricted according to what the
             pattern specifies *)

          |> Vars.add_vars (Vars.Tag.local_vars vars)
          (* vars above the current position are unrestricted,
             i.e. local vars *)
        in
        let env = Env.{
            vars = pat_vars; 
            table;
            ty_vars = params.ty_vars;
            se_vars = params.se_vars;
            (* TODO: sevars: do not construct a full environment each time? *)
            system = context; }
        in

        (* Check that all type variables have been infered.
           Remark: type unification environments are stateful *)
        match Infer.close env ienv with
        | Infer.FreeTyVars
        | Infer.FreeSystemVars
        | Infer.BadInstantiation _ ->
          s, `Continue

        | Infer.Closed tsubst ->
          (* we found the rewrite instance *)
          let subst =
            match Match.Mvar.to_subst ~mode:`Match table pat_vars mv with
            | `Subst subst -> subst
            | `BadInst pp_err ->
              soft_failure
                (Failure (Fmt.str "@[<hv 2>rewrite failed:@ @[%t@]@]" pp_err))
          in

          (* Substitute [mv] and [tsubst] *)
          let do_subst t = Term.gsubst tsubst (Term.subst subst t) in

          let left  = do_subst op_rule.pat.pat_op_term in
          let right = do_subst op_rule.right in
          let found_conds = List.map do_subst conds in
          let found_subs  = List.map do_subst op_rule.subs in

          let found_pat = Term.{ 
              pat_op_term   = left;
              pat_op_params = Params.Open.empty;
              pat_op_vars   = []; 
            } 
          in

          let found_instance =
            `Found {
              ienv;
              pat    = found_pat;
              right;
              system = se;
              vars; 
              conds  = found_conds;
              subgs  = found_subs;
            }
          in
          
          found_instance, `Map right
  in
  doit

(*------------------------------------------------------------------*)
(** {2 Rewrite at head position} *)

(** Exported *)
let rewrite_head
    (table  : Symbols.table)
    (params : Params.t)
    (env    : Vars.env)
    (ec     : Macros.expand_context)
    (hyps   : Hyps.TraceHyps.hyps)
    (sexpr  : SE.t)
    (rule   : rw_rule)
    (t      : Term.term) : (Term.term * (SE.arbitrary * Term.term) list) option
  =
  assert (rule.rw_kind = GlobalEq);
  match rw_inst ec table params env hyps rule t sexpr [] [] Pos.root `False with
  | _, `Continue -> None
  | `Found inst, `Map t ->
    Some (t, subgoals_of_found inst)
  | _ -> assert false

(*------------------------------------------------------------------*)
(** {2 Whole-term rewriting} *)

type rw_res = Equiv.any_form * (SE.context * Term.term) list

type rw_res_opt = 
  | RW_Result of rw_res
  | RW_Failed of error

(*------------------------------------------------------------------*)
(** Internal *)
let do_rewrite
    (table  : Symbols.table)
    (params : Params.t)
    (env    : Vars.env)
    (system : SE.context)
    (expand_context : Macros.expand_context)
    (hyps   : Hyps.TraceHyps.hyps)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res
  =
  let check_max_rewriting : unit -> unit =
    let cpt_occ = ref 0 in
    fun () ->
      if !cpt_occ > 1000 then   (* hard-coded *)
        raise (Failed MaxNestedRewriting);
      incr cpt_occ;
  in

  (* Attempt to find an instance of [left], and rewrites all occurrences of
     this instance.
     Return: (f, subs) *)
  let rec do_rewrite1
      (mult : Args.rw_count) (f : Equiv.any_form) 
    : 
      Equiv.any_form * (SE.t * Term.term) list
    =
    check_max_rewriting ();


    let s, f = 
      let s = `False in      (* we haven't found a instance yet *)
      match f with
      | Global f when rule.rw_kind = GlobalEq ->
        let s, _, f = 
          Pos.map_fold_e (rw_inst expand_context table params env hyps rule) system s f 
        in
        s, Equiv.Global f

      | Local f ->
        let s, _, f = 
          Pos.map_fold (rw_inst expand_context table params env hyps rule) system.set s f 
        in
        s, Equiv.Local f

      | _ -> s, f
    in

    match mult, s with
    | (Args.Any | Args.Exact 0), `False -> f, []

    | (Args.Once | Args.Many | Args.Exact _), `False -> 
      raise (Failed NothingToRewrite)

    | Args.Once, `Found inst -> f, subgoals_of_found inst

    | Args.Exact i, `Found inst ->
      let inst_subgs = subgoals_of_found inst in
      if i = 1 then f, inst_subgs 
      else
        let f, rsubs' = do_rewrite1 Args.(Exact (i - 1)) f in
        f, List.rev_append inst_subgs rsubs'

    | (Args.Many | Args.Any), `Found inst  ->
      let inst_subgs = subgoals_of_found inst in
      let f, rsubs' = do_rewrite1 Args.Any f in
      f, List.rev_append inst_subgs rsubs'
  in

  let f, subs = 
    if mult = Args.Exact 0 then (target, []) else do_rewrite1 mult target 
  in
  let subs = List.rev_map (fun (se, t) -> { system with set = se; }, t) subs in
  f, subs

(*------------------------------------------------------------------*)
(** Exported *)
let rewrite
    (table  : Symbols.table)
    (params : Params.t)
    (env    : Vars.env)
    (system : SE.context)
    (expand_context : Macros.expand_context)
    (hyps   : Hyps.TraceHyps.hyps)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res_opt
  =
  try
    let r =
      do_rewrite table params env system expand_context hyps mult rule target
    in
    RW_Result r
  with
  | Failed e -> RW_Failed e

(** Exported *)
let rewrite_exn   
    ~(loc   : L.t)
    (table  : Symbols.table)
    (params : Params.t)
    (env    : Vars.env)
    (system : SE.context)
    (expand_context : Macros.expand_context)
    (hyps   : Hyps.TraceHyps.hyps)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res
  =
  try
    do_rewrite table params env system expand_context hyps mult rule target
  with
  | Failed e -> recast_error ~loc e

(*------------------------------------------------------------------*)
(** {2 Higher-level rewrite} *)

let high_rewrite
    ~(mode   : [`TopDown of bool | `BottomUp])
    ~(strict : bool)
    (table   : Symbols.table)
    (params  : Params.t)
    (env     : Vars.env)
    (system  : SE.t)
    (mk_rule : Vars.vars -> Pos.pos -> rw_rule option) 
    (t       : Term.term)
  : Term.term 
  =
  let hyps = Hyps.TraceHyps.empty in

  let rw_inst : Pos.f_map = 
    fun occ se vars conds p ->
      (* build the rule to apply at position [p] using mk_rule *)
      match mk_rule vars p with
      | None -> `Continue
      | Some rule ->
        assert (rule.rw_kind = GlobalEq);
        assert (rule.rw_conds = []);
        
        let s = `False in       (* we have not found an instance yet *)
        match rw_inst InSequent table params env hyps rule occ se vars conds p s with
        | _, `Continue -> assert (not strict); `Continue
        | _, `Map t -> `Map t
  in

  let _, f = Pos.map ~mode rw_inst system t in
  f
