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
    (systems : SE.t) 
  : rw_state
  = 
  let left, right = rule.rw_rw in

  let projs, psubst = 
    SE.mk_proj_subst ~strict:false ~src:rule.rw_system ~dst:systems 
  in

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
    (table : Symbols.table) (env : Vars.env) (hyps : Hyps.TraceHyps.hyps Lazy.t) 
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
              Hyps.TraceHyps.add AnyName (Local cond) hyps
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
              Match.T.try_match ~expand_context ~hyps ~env table context occ inst.pat 
            with
            | NoMatch _ | FreeTyv -> s, `Continue
            | Match _mv -> 
              (* project the already found instance with the projections
                 applying to the current subterm *)
              s, `Map (Term.project_opt projs inst.right)
          end

      | `False ->
        (* project the pattern *)
        let pat_proj = Term.project_tpat_opt projs s.init_pat in

        let context = SE.reachability_context se in
        match 
          Match.T.try_match ~expand_context ~hyps ~env table context occ pat_proj 
        with
        | NoMatch _ | FreeTyv -> s, `Continue

        (* head matches *)
        | Match mv -> 
          (* we found the rewrite instance *)
          let subst =
            let pat_vars =
              Vars.add_vars pat_proj.pat_vars env
              (* vars in the pattern are restricted according to what the pattern specifies *)

              |> Vars.add_vars (Vars.Tag.local_vars vars)
              (* vars above the current position are unrestricted, i.e. local vars*)
            in
            match Match.Mvar.to_subst ~mode:`Match table pat_vars mv with
            | `Subst subst -> subst
            | `BadInst pp_err ->
              soft_failure (Failure (Fmt.str "@[<hv 2>rewrite failed:@ @[%t@]@]" pp_err))
          in
          
          let left = Term.subst subst pat_proj.pat_term in
          let right = 
            let right_proj = Term.project_opt projs s.init_right in
            Term.subst subst right_proj
          in
          let found_subs =
            List.map (fun rsub ->
                let rsub = Term.project_opt projs rsub in
                se, 
                Term.mk_forall ~simpl:true vars
                  (Term.mk_impls ~simpl:true conds (Term.subst subst rsub))
              ) s.init_subs
          in

          let found_pat = Term.{ 
              pat_term   = left;
              pat_tyvars = [];
              pat_vars   = []; 
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
    (env : Vars.env)
    (expand_context : Macros.expand_context)
    (hyps  : Hyps.TraceHyps.hyps Lazy.t)
    (sexpr : SE.t)
    (rule  : rw_rule)
    (t     : Term.term) : (Term.term * (SE.arbitrary * Term.term) list) option
  =
  let s = mk_state rule sexpr in
  match rw_inst expand_context table env hyps t sexpr [] [] Pos.root s with
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
(** Internal *)
let do_rewrite
    (table  : Symbols.table)
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

  (* Build the rewrite state corresponding to the rewrite rule [rule] and the 
     systems applying to [target].
     This may require renaming projections in [rule], and removing some
     projections from [rule]. *)
  let s = 
    let target_systems : SE.t =
      match target with
      | Global _ -> (oget system.pair :> SE.t)
      | Local _ -> system.set
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
      | Global f ->
        let s, _, f = 
          Pos.map_fold_e (rw_inst expand_context table env hyps) system s f 
        in
        s, Equiv.Global f

      | Local f ->
        let s, _, f = 
          Pos.map_fold (rw_inst expand_context table env hyps) system.set s f 
        in
        s, Equiv.Local f
    in

    match mult, s.found_instance with
    | (Args.Any | Args.Exact 0), `False -> f, []

    | (Args.Once | Args.Many | Args.Exact _), `False -> 
      raise (Failed NothingToRewrite)

    | Args.Once, `Found inst -> f, inst.subgs

    | Args.Exact i, `Found inst ->
      if i = 1 then f, inst.subgs 
      else
        let f, rsubs' = _rewrite Args.(Exact (i - 1)) f in
        f, List.rev_append inst.subgs rsubs'

    | (Args.Many | Args.Any), `Found inst  ->
      let f, rsubs' = _rewrite Args.Any f in
      f, List.rev_append inst.subgs rsubs'
  in

  let f, subs = 
    if mult = Args.Exact 0 then (target, []) else _rewrite mult target 
  in
  let subs = List.rev_map (fun (se, t) -> { system with set = se; }, t) subs in
  f, subs

(*------------------------------------------------------------------*)
(** Exported *)
let rewrite
    (table  : Symbols.table)
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
      do_rewrite table env system expand_context hyps mult rule target
    in
    RW_Result r
  with
  | Failed e -> RW_Failed e

(** Exported *)
let rewrite_exn   
    ~(loc   : L.t)
    (table  : Symbols.table)
    (env    : Vars.env)
    (system : SE.context)
    (expand_context : Macros.expand_context)
    (hyps   : Hyps.TraceHyps.hyps)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res
  =
  try
    do_rewrite table env system expand_context hyps mult rule target
  with
  | Failed e -> recast_error ~loc e

(*------------------------------------------------------------------*)
(** {2 Higher-level rewrite} *)

let high_rewrite
    ~(mode   : [`TopDown of bool | `BottomUp])
    ~(strict : bool)
    (table   : Symbols.table)
    (env     : Vars.env)
    (system  : SE.t)
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
        
        let state = mk_state rule se in
        match rw_inst InSequent table env hyps occ se vars conds p state with
        | _, `Continue -> assert (not strict); `Continue
        | _, `Map t -> `Map t
  in

  let _, f = Pos.map ~mode rw_inst system t in
  f
