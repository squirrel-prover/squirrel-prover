open Utils
open Rewrite

module Args = TacticsArgs
module L = Location

module St = Term.St
module Sv = Vars.Sv

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
let dbg ?(force=false) s =
  let mode = if Config.debug_tactics () || force then `Dbg else `Ignore in
  Printer.prt mode s

(*------------------------------------------------------------------*)
let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let bad_args () = hard_failure (Failure "improper arguments")

(*------------------------------------------------------------------*)
(** {2 Functor building tactics from a Sequent module}*)

module LowTac (S : Sequent.S) = struct

  module Hyps = S.Hyps

  (*------------------------------------------------------------------*)
  (** {3 Miscellaneous} *)

  (*------------------------------------------------------------------*)
  let bad_args () = hard_failure (Failure "improper arguments")

  (*------------------------------------------------------------------*)
  let wrap_fail f (s: S.sequent) sk fk =
    try sk (f s) fk with
    | Tactics.Tactic_soft_failure e -> fk e

  (*------------------------------------------------------------------*)
  let check_ty_eq ?loc ty1 ty2 = 
    if not (Type.equal ty1 ty2) then
      soft_failure ?loc 
        (Failure (Fmt.strf "types %a and %a are not compatible" 
                    Type.pp ty1 Type.pp ty2));
    ()

  (*------------------------------------------------------------------*)
  let check_hty_eq ?loc hty1 hty2 = 
    if not (Type.ht_equal hty1 hty2) then
      soft_failure ?loc
        (Failure (Fmt.strf "types %a and %a are not compatible" 
                    Type.pp_ht hty1 Type.pp_ht hty2));
    ()

  (*------------------------------------------------------------------*)
  (** {3 Conversion} *)

  let convert_args (s : S.sequent) args sort = 
    Args.convert_args (S.table s) (S.ty_vars s) (S.env s) args sort

  let convert_i ?pat (s : S.sequent) term = 
    let cenv = Theory.{ table = S.table s; cntxt = InGoal; } in 
    Theory.convert_i ?pat cenv (S.ty_vars s) (S.env s) term

  let econvert (s : S.sequent) term = 
    let cenv = Theory.{ table = S.table s; cntxt = InGoal; } in 
    Theory.econvert cenv (S.ty_vars s) (S.env s) term

  let convert_ht (s : S.sequent)  ht =
    let env = S.env s in
    let table = S.table s in
    let conv_env = Theory.{ table = table; cntxt = InGoal; } in
    Theory.convert_ht conv_env (S.ty_vars s) env ht

  (*------------------------------------------------------------------*)
  (** Parse a partially applied lemma or hypothesis as a pattern. *)
  let convert_pt_hol (pt : Theory.p_pt_hol) (s : S.sequent) : 
    Goal.ghyp * Type.message Term.pat = 
    let lem = S.get_reach_hyp_or_lemma pt.p_pt_hid s in
    let f_args, f = Term.decompose_forall lem.gc_concl in
    let f_args, subst = Term.erefresh_vars `Global f_args in
    let f = Term.subst subst f in

    let pt_args_l = List.length pt.p_pt_args in

    if List.length f_args < pt_args_l then
      hard_failure ~loc:(L.loc pt.p_pt_hid)  (Failure "too many arguments");

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
    let f = Term.subst subst f in

    let pat = Term.{ 
        pat_tyvars = lem.gc_tyvars;
        pat_vars = !pat_vars;
        pat_term = f; } 
    in      
    lem.gc_name, pat

  (*------------------------------------------------------------------*)
  let make_exact ?loc env ty name =  
    match Vars.make_exact env ty name with
    | None ->
      hard_failure ?loc
        (Tactics.Failure ("variable name " ^ name ^ " already used"))
    | Some v' -> v'

  let make_exact_r ?loc env ty name =  
    match Vars.make_exact_r env ty name with
    | None ->
      hard_failure ?loc
        (Tactics.Failure ("variable name " ^ name ^ " already used"))
    | Some v' -> v'

  (*------------------------------------------------------------------*)
  (** {3 Targets} *)
  type target = 
    | T_goal
    | T_hyp of Ident.t
    | T_felem of int       (* frame element in an equiv *)

  type targets = target list

  let target_all s : target list =
    T_goal :: List.map (fun ldecl -> T_hyp (fst ldecl)) (Hyps.to_list s)

  let make_single_target (symb : lsymb) (s : S.sequent) : target =
    let name = L.unloc symb in

    let error () = 
      soft_failure ~loc:(L.loc symb)
        (Tactics.Failure ("unknown hypothesis or frame element " ^ name))
    in

    if Hyps.mem_name name s then
      T_hyp (fst (Hyps.by_name symb s))
    else
      match int_of_string_opt name with
      | Some i ->
        if S.mem_felem i s then T_felem i else error ()
      | None -> error ()

  let make_in_targets (in_t : Args.in_target) (s : S.sequent) : targets * bool =
    match in_t with
    | `Hyps symbs -> 
      List.map (fun symb -> make_single_target symb s) symbs, false
    | `All -> target_all s, true
    | `Goal -> [T_goal], false

  (*------------------------------------------------------------------*)
  (** Formulas of different types *)
  type cform = 
    | Cform  of S.form
    | Ctform of Term.message

  let mk_form f  = Cform  f
  let mk_tform f = Ctform f

  (*------------------------------------------------------------------*)
  let subst_cform subst = function
    | Ctform f -> Ctform (Term.subst subst f)
    | Cform  f -> Cform  (S.subst_hyp subst f)

  (** Apply some function [doit] to a single target. *)
  let do_target 
      (doit : (cform * Ident.t option) -> cform * S.form list) 
      (s : S.sequent) (t : target) : S.sequent * S.sequent list =
    let f, s, tgt_id = match t with
      | T_goal    -> Cform  (S.goal s       ),               s , None
      | T_hyp id  -> Cform  (Hyps.by_id id s), Hyps.remove id s, Some id
      | T_felem i -> Ctform (S.get_felem i s),               s , None
    in

    let f,subs = doit (f,tgt_id) in
    let subs : S.sequent list = 
      List.map (fun sub -> S.set_goal sub s) subs
    in

    match t, f with
    | T_goal,    Cform  f -> S.set_goal f s, subs
    | T_hyp id,  Cform  f -> Hyps.add (Args.Named (Ident.name id)) f s, subs
    | T_felem i, Ctform f -> S.change_felem i [f] s, subs
    | _ -> assert false

  let do_targets doit (s : S.sequent) targets : S.sequent * S.sequent list = 
    let s, subs = 
      List.fold_left (fun (s,subs) target ->
          let s, subs' = do_target doit s target in
          s, (List.rev subs') @ subs
        ) (s,[]) targets
    in
    s, List.rev subs


  (*------------------------------------------------------------------*)
  (** {3 Macro unfolding}*)

  let unfold_macro : type a. a Term.term -> S.sequent -> Term.esubst list = 
    fun t s ->
    match t with
    | Macro (ms,l,a) ->
      if not (S.query_happens ~precise:true s a) then
        soft_failure (Tactics.MustHappen a);

      let mdef = Macros.get_definition (S.mk_trace_cntxt s) ms a in

      [Term.ESubst (Macro (ms,l,a), mdef)]

    | _ -> 
      soft_failure (Tactics.Failure "can only expand macros")

  let unfold_macro : type a. 
    canfail:bool -> a Term.term -> S.sequent -> Term.esubst list = 
    fun ~canfail t s ->
    try unfold_macro t s with
    | Tactics.Tactic_soft_failure _ when not canfail -> []


  let expand_macro (targets : targets) (t : 'a Term.term) (s : S.t) : S.t =
    let subst = unfold_macro ~canfail:true t s in
    if subst = [] then soft_failure (Failure "nothing to expand");

    let doit (f,_) = subst_cform subst f, [] in
    let s, subs = do_targets doit s targets in
    assert (subs = []);
    s

  (** find occurrences of a macro in a formula *)
  let find_occs_macro_term : type a. 
    ?st:St.t ->
    [`Any | `MSymb of Symbols.macro Symbols.t] ->
    a Term.term -> Term.St.t =
    fun ?(st=Term.St.empty) m t -> 

    let cond ms = m = `MSymb ms.Term.s_symb || m = `Any in

    let rec find st (Term.ETerm t) = 
      let st = match t with
        | Macro (ms, _, _) when cond ms -> 
          Term.St.add (Term.ETerm t) st
        | _ -> st in

      (* we do not recurse under binders *)
      (* FIXME: expand under binders *)
      match t with
      | ForAll _ | Exists _ | Find _ | Seq _ -> st
      | _ -> Term.tfold (fun t st -> find st t) t st
    in

    find st (ETerm t)

  let find_occs_macro_terms ~st m terms =
    List.fold_left (fun occs t -> find_occs_macro_term ~st:occs m t) st terms

  (** find occurrences of a macro in a sequent *)
  let find_occs_macro 
      (m : [`Any | `MSymb of Symbols.macro Symbols.t])
      (targets : targets) (s : S.t) : Term.St.t =
    List.fold_left (fun occs target -> 
        let terms = match target with
          | T_goal    -> S.get_terms (S.goal s)
          | T_hyp id  -> S.get_terms  (Hyps.by_id id s)
          | T_felem i -> [S.get_felem i s]
        in
        find_occs_macro_terms ~st:occs m terms
      ) St.empty targets

  let subst_of_occs_macro ~(canfail : bool) (occs : Term.St.t) s : Term.subst =
    Term.St.fold (fun (ETerm t) subst -> 
        unfold_macro ~canfail t s @ subst
      ) occs [] 

  (** expand all macros in a term *)
  let expand_all_term : type a. a Term.term -> S.sequent -> a Term.term =   
    fun term s ->

    let rec expand_rec term =
      let occs = find_occs_macro_term `Any term in
      let subst = subst_of_occs_macro ~canfail:false occs s in
      if subst = [] then term else expand_rec (Term.subst subst term) 
    in

    expand_rec term

  (** expand all macro of some targets in a sequent *)
  let expand_all targets (s : S.sequent) : S.sequent = 
    let targets, all = make_in_targets targets s in
    let canfail = not all in

    let rec expand_rec s =
      let occs = find_occs_macro `Any targets s in
      let subst = subst_of_occs_macro ~canfail occs s in
      if subst = [] then s else expand_rec (S.subst subst s)
    in

    expand_rec s

  let expand_all_l tgts s : S.sequent list = [expand_all tgts s]

  let expand (targets : target list) (arg : Theory.term) (s : S.t) : S.t = 
    let tbl = S.table s in
    match Args.convert_as_lsymb [Args.Theory arg] with
    | Some m ->
      let m = Symbols.Macro.of_lsymb m tbl in
      let occs = find_occs_macro (`MSymb m) targets s in
      let subst = 
        Term.St.fold (fun (ETerm t) subst -> 
            unfold_macro ~canfail:false t s @ subst
          ) occs [] in

      if subst = [] then soft_failure (Failure "nothing to expand");

      let doit (f,_) = subst_cform subst f, [] in
      let s, subs = do_targets doit s targets in
      assert (subs = []);
      s

    | _ ->
      match convert_args s [Args.Theory arg] Args.(Sort Message) with
      | Args.Arg (Args.Message (f, _)) ->
        expand_macro targets f s

      | _ ->
        hard_failure (Tactics.Failure "expected a message term")

  let expands (args : Theory.term list) (s : S.t) : S.t =
    List.fold_left (fun s arg -> expand (target_all s) arg s) s args 

  (*------------------------------------------------------------------*)
  (** {3 Rewriting types and functions}*)

  type rw_arg = 
    | Rw_rw of Ident.t option * rw_erule
    (* The ident is the ident of the hyp the rule came from (if any) *)

    | Rw_expand of Theory.term

  type rw_earg = Args.rw_count * rw_arg
  
  (** [rewrite ~all tgt rw_args] rewrites [rw_arg] in [tgt].
      If [all] is true, then does not fail if no rewriting occurs. *)
  let rewrite ~all 
      (targets: target list) 
      (rw : Args.rw_count * Ident.t option * rw_erule) (s : S.sequent)
    : S.sequent * S.sequent list =
    let found1, cpt_occ = ref false, ref 0 in

    (* Return: (f, subs) *)
    let rec doit
      : type a. Args.rw_count -> a rw_rule -> cform -> cform * Term.form list = 
      fun mult (tyvars, sv, rsubs, l, r) f ->

        let subs_r = ref [] in

        (* Substitute [occ] by [r] (where free variables
           are instantiated according to [mv], and variables binded above the
           matched occurrences are universally quantified in the generated 
           sub-goals. *)
        let rw_inst occ vars mv =
          if !cpt_occ > 1000 then   (* hard-coded *)
            hard_failure (Failure "max nested rewriting reached (1000)");
          incr cpt_occ;
          found1 := true;

          let subst = S.Match.to_subst mv in
          let r = Term.cast (Term.kind occ) (Term.subst subst r) in
          let rsubs = 
            List.map (fun rsub ->
                Term.mk_forall ~simpl:true vars (Term.subst subst rsub)
              ) rsubs 
          in
          subs_r := rsubs;
          r
        in

        (* tries to find an occurence of [l] and rewrite it. *)
        let pat = 
          Term.{ pat_tyvars = tyvars; pat_vars = sv; pat_term = l; } 
        in
        let many = match mult with `Once -> false | `Any | `Many -> true in

        let f_opt = match f with
          | Cform f -> 
            let f_opt = S.Match.find_map ~many (S.env s) f pat rw_inst in
            omap mk_form f_opt

          | Ctform f -> 
            let f_opt = Term.Match.find_map ~many (S.env s) f pat rw_inst in
            omap mk_tform f_opt
        in

        match mult, f_opt with
        | `Any, None -> f, !subs_r

        | (`Once | `Many), None -> 
          if not all 
          then soft_failure Tactics.NothingToRewrite 
          else f, !subs_r

        | (`Many | `Any), Some f -> 
          let f, rsubs' = doit `Any (tyvars, sv, rsubs, l, r) f in
          f, List.rev_append (!subs_r) rsubs'

        | `Once, Some f -> f, !subs_r
    in

    let is_same (hyp_id : Ident.t option) (target_id : Ident.t option) = 
      match hyp_id, target_id with
      | None, _ | _, None -> false
      | Some hyp_id, Some target_id ->
        Ident.name hyp_id = Ident.name target_id && 
        Ident.name hyp_id <> "_" 
    in

    let doit_tgt (f,tgt_id : cform * Ident.t option) : cform * S.form list =
      match rw with
      | mult,  id_opt, (tyvars, sv, subs, Term.ESubst (l,r)) ->
        if is_same id_opt tgt_id 
        then f, []
        else
          let f, subs = doit mult (tyvars, sv, subs, l, r) f in
          let subs = List.rev subs in
          f, List.map S.reach_to_form subs
    in

    let s, subs = do_targets doit_tgt s targets in

    if all && not !found1 then soft_failure Tactics.NothingToRewrite;

    s, subs

  (** Parse rewrite tactic arguments as rewrite rules with possible subgoals 
      showing the rule validity. *)
  let p_rw_item (rw_arg : Args.rw_item) s : rw_earg * S.sequent list =
    let p_rw_rule dir (p_pt : Theory.p_pt_hol) 
      : rw_erule * S.sequent list * Ident.t option = 
      let ghyp, pat = convert_pt_hol p_pt s in
      let id_opt = match ghyp with `Hyp id -> Some id | _ -> None in

      (* We are using an hypothesis, hence no new sub-goals *)
      let premise = [] in

      pat_to_rw_erule dir pat, premise, id_opt
    in

    let p_rw_item (rw_arg : Args.rw_item) : rw_earg * (S.sequent list) = 
      let rw, subgoals = match rw_arg.rw_type with
        | `Rw f -> 
          let dir = L.unloc rw_arg.rw_dir in
          (* (rewrite rule, subgols, hyp id) if applicable *)
          let rule, subgoals, id_opt = p_rw_rule dir f in
          Rw_rw (id_opt, rule), subgoals

        | `Expand t -> 
          if L.unloc rw_arg.rw_dir <> `LeftToRight then
            hard_failure ~loc:(L.loc rw_arg.rw_dir) 
              (Failure "expand cannot take a direction");

          Rw_expand t, []
      in
      (rw_arg.rw_mult, rw), subgoals
    in

    p_rw_item rw_arg

  (** Applies a rewrite item *)
  let do_rw_item 
      (rw_item : Args.rw_item) (rw_in : Args.in_target) (s : S.sequent) 
    : S.sequent list =
    let targets, all = make_in_targets rw_in s in
    let (rw_c,rw_arg), subgoals = p_rw_item rw_item s in

    match rw_arg with
    | Rw_rw (id, erule) -> 
      let s, subs = rewrite ~all targets (rw_c, id, erule) s in
      subgoals @                  (* prove rule *)
      subs @                      (* prove instances premisses *)
      [s]                         (* final sequent *)

    | Rw_expand arg -> [expand targets arg s]


  (*------------------------------------------------------------------*)
  (** {3 Case tactic}*)
  (** Type for case and destruct tactics handlers *)
  type c_handler =
    | CHyp of Ident.t

  type c_res = c_handler * S.sequent

  (** Case analysis on a timestamp *)
  let timestamp_case (ts : Term.timestamp) s : S.sequent list =
    let system = S.system s in
    let table  = S.table s in

    let mk_case descr : Vars.evar list * Term.timestamp =
      let env = ref (S.env s) in
      let indices, s = Term.refresh_vars (`InEnv env) descr.Action.indices in

      let name =
        SystemExpr.action_to_term table system
          (Action.subst_action s descr.Action.action)
      in
      (* FIXME: is this second substitution useful ? *)
      let name = Term.subst s name in

      List.map (fun x -> Vars.EVar x) indices, name
    in

    let cases = SystemExpr.map_descrs table system mk_case in

    List.map (fun (indices, ts_case) ->
        let ts_subst =
          if indices = [] then [Term.ESubst (ts, ts_case)] else []
        in
        let goal = S.subst_hyp ts_subst (S.goal s) in
        let prem =
          Term.mk_exists indices
            (Term.Atom (`Timestamp (`Eq,ts, ts_case)))
        in
        let prem = S.reach_to_form prem in
        S.set_goal (S.Smart.mk_impl ~simpl:false prem goal) s
      ) cases

  (** Case analysis on disjunctions in an hypothesis.
      When [nb=`Any], recurses.
      When [nb=`Some l], destruct at most [l]. *)
  let hypothesis_case ~nb id (s : S.sequent) : c_res list =
    let destr_err () = soft_failure (Failure "not a disjunction") in

    let rec case acc form = match S.Smart.destr_or form with
      | Some (f,g) -> case (case acc g) f
      | None       -> form :: acc in

    let form = Hyps.by_id id s in
    let s = Hyps.remove id s in

    let cases = match nb with
      | `Any -> case [] form
      | `Some l -> match S.Smart.destr_ors l form with
        | None -> destr_err ()
        | Some cases -> cases
    in

    if cases = [] then destr_err ();

    List.map (fun g ->
        let ng = Ident.name id in
        let idg, sg = Hyps.add_i (Args.Named ng) g s in
        ( CHyp idg, sg )
      ) cases

  (*------------------------------------------------------------------*)
  (** Reduce *)
  let reduce_sequent s = S.map (S.reduce s) s        

  (*------------------------------------------------------------------*)
  (** Revert *)
  let revert (hid : Ident.t) (s : S.t) : S.t =
    let f = Hyps.by_id hid s in
    let s = Hyps.remove hid s in
    S.set_goal (S.Smart.mk_impl ~simpl:false f (S.goal s)) s

  let revert_str (hyp_name : lsymb) s : S.t =
    let hid,_ = Hyps.by_name hyp_name s in
    revert hid s

  let revert_args (args : Args.parser_arg list) s : S.t list =
    let s =
      List.fold_left (fun s arg -> match arg with
          | Args.String_name arg -> revert_str arg s
          | _ -> bad_args ()
        ) s args in
    [s]

  let revert_tac args s sk fk = wrap_fail (revert_args args) s sk fk

end
