open Utils

module Args = TacticsArgs
module SE   = SystemExpr

(*------------------------------------------------------------------*)
(** A rewrite rule.
    Invariant: if
    [{ rw_tyvars = tyvars; rw_vars = sv; rw_conds = φ; rw_rw = (l,r); }]
    is a rewrite rule, then:
    - sv ⊆ FV(l) *)
type rw_rule = {
  rw_tyvars : Type.tvars;            (** type variables *)
  rw_system : SE.t;                  (** systems the rule applies to *)
  rw_vars   : Vars.Sv.t;             (** term variables *)
  rw_conds  : Term.term list;        (** premises *)
  rw_rw     : Term.term * Term.term; (** pair (source, destination) *)
}

let pp_rw_rule fmt (rw : rw_rule) =
  let pp_tys fmt tys = 
    if tys = [] then () else
      Fmt.pf fmt "[%a] " (Fmt.list Type.pp_tvar) tys
  in
  let pp_vars fmt vars = 
    if Vars.Sv.is_empty vars then () else
      Fmt.pf fmt "%a " Vars.pp_typed_list (Vars.Sv.elements vars)
  in
  let pp_conds fmt conds =
    if conds = [] then () else
      Fmt.pf fmt " when %a" (Fmt.list Term.pp) conds
  in
  
  let src, dst = rw.rw_rw in
  Fmt.pf fmt "%a%a: %a -> %a%a"
    pp_tys rw.rw_tyvars
    pp_vars rw.rw_vars
    Term.pp src Term.pp dst
    pp_conds rw.rw_conds

(*------------------------------------------------------------------*)
(** Check that the rule is correct. *)
let check_rule (rule : rw_rule) : unit =
  let l, r = rule.rw_rw in

  if not (Vars.Sv.subset rule.rw_vars (Term.fv l)) then
    Tactics.hard_failure Tactics.BadRewriteRule;
  ()

(** Make a rewrite rule from a formula *)
let pat_to_rw_rule ?loc 
    ~(destr_eq : Term.term -> (Term.term * Term.term) option)
    (system    : SE.arbitrary) 
    (dir       : [< `LeftToRight | `RightToLeft ])
    (p         : Term.term Match.pat) 
  : rw_rule 
  =
  let subs, f = Term.decompose_impls_last p.pat_term in

  let e = match destr_eq f with
    | Some (t1, t2) -> t1,t2
    | _ -> Tactics.hard_failure ?loc (Tactics.Failure "not an equality")
  in

  let e = match dir with
    | `LeftToRight -> e
    | `RightToLeft ->
      let t1,t2 = e in
      t2,t1
  in

  let rule = {
    rw_tyvars = p.pat_tyvars;
    rw_system = system;
    rw_vars   = p.pat_vars;
    rw_conds  = subs;
    rw_rw     = e;
  } in

  (* We check that the rule is valid *)
  check_rule rule;

  rule

(*------------------------------------------------------------------*)
(** Internal exception *)
exception NoRW

(*------------------------------------------------------------------*)
let _rewrite_head
    (table  : Symbols.table)
    (system : SE.t)
    (rule   : rw_rule)
    (t      : Term.term) : Term.term * Term.term list
  =
  (* FEATURE: allow [rewrite_head] to rewrite rules that do not apply to 
     all systems. *)
  assert (SE.subset table rule.rw_system SE.any);

  let l, r = rule.rw_rw in

  let pat = Match.{ 
      pat_tyvars = rule.rw_tyvars; 
      pat_vars   = rule.rw_vars; 
      pat_term   = l; }
  in

  let mv =
    match Match.T.try_match table system t pat with
    | FreeTyv | NoMatch _ -> raise NoRW
    | Match mv -> mv
  in
  let subst = Match.Mvar.to_subst ~mode:`Match mv in
  let r = Term.subst subst r in
  let subs = List.map (Term.subst subst) rule.rw_conds in
  r, subs

let rewrite_head
    (table  : Symbols.table)
    (system : SE.t)
    (rule   : rw_rule)
    (t      : Term.term) : (Term.term * Term.term list) option
  =
  try Some (_rewrite_head table system rule t) with NoRW -> None

(*------------------------------------------------------------------*)
type rw_res = [
  | `Result of Equiv.any_form * (SE.context * Term.term) list
  | `NothingToRewrite
  | `MaxNestedRewriting
  | `RuleBadSystems of string
]

(*------------------------------------------------------------------*)
(** as an instance been found:
    - [pat]: pattern of the instance found (no free variables left)
    - [right]: right term instantiated with the instance found
    - [system]: systems applying to the instance found *) 
type found = { 
  pat    : Term.term Match.pat; 
  right  : Term.term;
  system : SE.t; 
  subgs  : (SE.context * Term.term) list;
}

type rw_state = { 
  init_pat   : Term.term Match.pat;
  init_subs  : Term.term list;
  init_right : Term.term;

  found_instance : [ `False | `Found of found ];
}

(*------------------------------------------------------------------*)
(** Not exported *)
exception Failed of [
    | `NothingToRewrite
    | `MaxNestedRewriting
    | `RuleBadSystems of string
  ] 

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
            raise (Failed (`RuleBadSystems "system projection ambiguity"));

          Some (List.map fst l)
      end
  in

  let projs = omap (List.map snd) psubst in
  let psubst = odflt [] psubst in

  if projs = Some [] then
    raise (Failed (`RuleBadSystems "no system of the rule applies"));

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
  { init_pat = Match.{ 
        pat_tyvars = rule.rw_tyvars; 
        pat_vars   = rule.rw_vars; 
        pat_term   = mk_form left;
      };
    init_right = mk_form right;
    init_subs      = List.map mk_form rule.rw_conds;
    found_instance = `False; } 


(*------------------------------------------------------------------*)
(* If there is a match (with [mv]), substitute [occ] by [right] where
   free variables are instantiated according to [mv], and variables
   bound above the matched occurrences are universally quantified in
   the generated sub-goals. *)
let rw_inst
    (table : Symbols.table) (rule : rw_rule) (system : SE.context)
  : rw_state Match.Pos.f_map_fold 
  = 
  fun occ projs vars _conds _p (s : rw_state) ->
  (* project the system *)
  let system_set = SE.project_opt projs system.set in

  if not (SE.subset table system_set rule.rw_system) then 
    s, `Continue
  else 
    match s.found_instance with
    | `Found inst -> 
      (* we already found the rewrite instance earlier *)

      (* check if the same system apply to the subterm *)
      if not (SE.subset table system_set inst.system) then 
        s, `Continue 
      else
        begin match Match.T.try_match table system_set occ inst.pat with
          | NoMatch _ | FreeTyv -> s, `Continue
          | Match mv -> 
            (* project the already found instance with the projections
               applying to the current subterm *)
            s, `Map (Term.project_opt projs inst.right)
        end

    | `False ->
      (* project the pattern *)
      let pat_proj = Match.project_tpat_opt projs s.init_pat in
    
      match Match.T.try_match table system_set occ pat_proj with
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
              { system with set = system_set}, 
              Term.mk_forall ~simpl:true vars (Term.subst subst rsub)
            ) rule.rw_conds
        in

        let found_pat = Match.{ 
            pat_term   = left;
            pat_tyvars = [];
            pat_vars   = Sv.empty; 
          } in

        let found_instance = `Found {
            pat    = found_pat;
            right;
            system = system_set;
            subgs  = found_subs;
          } in

        { s with found_instance }, `Map right

(*------------------------------------------------------------------*)
let rewrite
    (table  : Symbols.table)
    (system : SE.context)
    (env    : Vars.env)
    (mult   : Args.rw_count)
    (rule   : rw_rule)
    (target : Equiv.any_form) : rw_res
  =
  let check_max_rewriting : unit -> unit =
    let cpt_occ = ref 0 in
    fun () ->
      if !cpt_occ > 1000 then   (* hard-coded *)
        raise (Failed `MaxNestedRewriting);
      incr cpt_occ;
  in

  (* Built the rewrite state corresponding the rewrite rule [rule] and the 
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

  (* Attempt to find an instance of [left], and rewrites all occurrences of
     this instance.
     Return: (f, subs) *)
  let rec _rewrite (mult : Args.rw_count) (f : Equiv.any_form) 
    : Equiv.any_form * (SE.context * Term.term) list
    =
    check_max_rewriting ();

    let s, f = match f with
      | `Equiv f ->
        let s, _, f = 
          Match.Pos.map_fold_e (rw_inst table rule system) env s f 
        in
        s, `Equiv f

      | `Reach f ->
        let s, _, f = 
          Match.Pos.map_fold (rw_inst table rule system) env s f 
        in
        s, `Reach f
    in

    match mult, s.found_instance with
    | `Any, `False -> f, []

    | (`Once | `Many), `False -> raise (Failed `NothingToRewrite)

    | (`Many | `Any), `Found inst  ->
      let f, rsubs' = _rewrite `Any f in
      f, List.rev_append inst.subgs rsubs'

    | `Once, `Found inst -> f, inst.subgs
  in

  match _rewrite mult target with
  | f, subs -> `Result (f, List.rev subs)

  | exception Failed (`NothingToRewrite)   -> `NothingToRewrite
  | exception Failed (`MaxNestedRewriting) -> `MaxNestedRewriting
  | exception Failed (`RuleBadSystems s)   -> `RuleBadSystems s
