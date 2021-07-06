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
(** {2 Functor building tactics from a Sequent module} *)

module LowTac (S : Sequent.S) = struct

  module Hyps = S.Hyps

  module S = struct

    include S

    let wrap_conc x = Equiv.Any.convert_from S.conc_kind x
    let unwrap_conc x = Equiv.Any.convert_to S.conc_kind x

    let wrap_hyp x = Equiv.Any.convert_from S.hyp_kind x
    let unwrap_hyp x = Equiv.Any.convert_to S.hyp_kind x

    let hyp_to_conc = Equiv.Babel.convert ~src:S.hyp_kind ~dst:S.conc_kind
    let hyp_of_conc = Equiv.Babel.convert ~dst:S.hyp_kind ~src:S.conc_kind

    let fv_conc = Equiv.Babel.fv S.conc_kind
    let fv_hyp = Equiv.Babel.fv S.hyp_kind

    let subst_conc = Equiv.Babel.subst S.conc_kind
    let subst_hyp = Equiv.Babel.subst S.hyp_kind

    let terms_of_conc = Equiv.Babel.get_terms S.conc_kind
    let terms_of_hyp = Equiv.Babel.get_terms S.hyp_kind

    let pp_hyp = Equiv.Babel.pp S.hyp_kind
    let pp_conc = Equiv.Babel.pp S.conc_kind

  end

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
  let happens_premise (s : S.t) (a : Term.timestamp) : S.t =
    let form = Term.mk_happens a in
    S.set_goal (S.unwrap_conc (`Reach form)) s

  (*------------------------------------------------------------------*)

  (** {3 Targets} *)
  type target = 
    | T_conc              (** Conclusion. *)
    | T_hyp   of Ident.t  (** Hypothesis. *)
    | T_felem of int      (** Element in conclusion biframe. *)

  (** Formulas and terms of different types, corresponding to different targets.
    * It is slight abusive to use [any_form] here: we represent frame elements
    * as local formulas, though local formulas must be boolean terms while
    * frame elements can be arbitrary messages. *)
  type cform = Equiv.any_form

  type targets = target list

  let target_all s : target list =
    T_conc :: List.map (fun ldecl -> T_hyp (fst ldecl)) (Hyps.to_list s)

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
    | `Goal -> [T_conc], false

  (** Apply some function [doit] to a single target. *)
  let do_target 
      (doit : (cform * Ident.t option) -> cform * S.conc_form list)
      (s : S.sequent) (t : target) : S.sequent * S.sequent list =
    let f, s, tgt_id = match t with
      | T_conc ->
          let f = S.wrap_conc (S.goal s) in
          f, s, None
      | T_hyp id ->
          let f = S.wrap_hyp (Hyps.by_id id s) in
          f, Hyps.remove id s, Some id
      | T_felem i ->
          let f = `Reach (S.get_felem i s) in
          f, s, None
    in

    let f,subs = doit (f,tgt_id) in
    let subs : S.sequent list = 
      List.map (fun sub -> S.set_goal sub s) subs
    in

    match t, f with
    | T_conc,    f -> S.set_goal (S.unwrap_conc f) s, subs
    | T_hyp id,  f -> Hyps.add (Args.Named (Ident.name id)) (S.unwrap_hyp f) s, subs
    | T_felem i, `Reach f -> S.change_felem i [f] s, subs
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
  (** {3 Macro unfolding} *)

  let _unfold_macro : type a. a Term.term -> S.sequent -> a Term.term = 
    fun t s ->
    match t with
    | Macro (ms,l,a) ->
      if not (S.query_happens ~precise:true s a) then
        soft_failure (Tactics.MustHappen a);

      Macros.get_definition (S.mk_trace_cntxt s) ms a 

    | _ -> 
      soft_failure (Tactics.Failure "can only expand macros")

  let unfold_macro : type a. 
    strict:bool -> a Term.term -> S.sequent -> a Term.term option = 
    fun ~strict t s ->
    try Some (_unfold_macro t s) with
    | Tactics.Tactic_soft_failure _ when not strict -> None

  let expand 
      (targets: target list) 
      (macro : [ `Msymb of Symbols.macro Symbols.t 
               | `Mterm of Term.message
               | `Any])
      (s : S.sequent) : bool * S.sequent
    =
    let found1 = ref false in

    let found_occ subst ms occ =
      match macro with
      | `Msymb mname -> ms.Term.s_symb = mname
      | `Mterm t -> Term.subst subst occ = t
      | `Any -> true
    in
    (* unfold_macro is not allowed to fail if we try to expand a specific term *)
    let strict =
      match macro with
      | `Mterm _ -> true
      | `Msymb _ | `Any -> false
    in      

    (* applies [doit] to all subterms of the target [f] *)
    let rec doit ((f,_) : cform * Ident.t option) : cform * S.conc_form list =

      let expand_inst (Term.ETerm occ) subst vars conds =
        let occ = match occ with
          | Term.Var _ -> Term.subst subst occ
          | _ -> occ
        in
                          
        match occ with
        | Term.Macro (ms, l, _) ->
          if found_occ subst ms occ then
            match unfold_macro ~strict (Term.subst subst occ) s with
            | None -> `Continue
            | Some t ->
              found1 := true;
              `Map (Term.ETerm t)
          else `Continue

        | _ -> `Continue
      in

      match f with
      | `Equiv f -> 
        let f = odflt f (Match.E.map expand_inst (S.env s) f) in
        `Equiv f, []
          
      | `Reach f ->
        let f = odflt f (Match.T.map expand_inst (S.env s) f) in
        `Reach f, []
    in

    let s, subs = do_targets doit s targets in
    assert (subs = []);

    !found1, s

  (** expand all macros in a term *)
  let rec expand_all_term (f : Term.message) (s : S.t) : Term.message =
    let expand_inst (Term.ETerm occ) subst vars conds =
      let occ = match occ with
        | Term.Var _ -> Term.subst subst occ
        | _ -> occ
      in

      match occ with
      | Term.Macro (ms, l, _) ->
        begin
          match unfold_macro ~strict:false (Term.subst subst occ) s with
          | None -> `Continue
          | Some t -> `Map (Term.ETerm t)
        end

      | _ -> `Continue
    in
    match Match.T.map expand_inst (S.env s) f with
    | None -> f
    | Some f -> expand_all_term f s 

  (** expand all macro of some targets in a sequent *)
  let expand_all targets (s : S.sequent) : S.sequent = 
    let rec aux_rec s =
      let targets, all = make_in_targets targets s in
      let found, s = expand targets `Any s in
      if found then aux_rec s else s
    in
    aux_rec s
      
  let expand_all_l tgts s : S.sequent list = [expand_all tgts s]
                                             
  let expand_arg (targets : target list) (arg : Theory.term) (s : S.t) : S.t =
    let expand targs macro s =
      let found, s = expand targets macro s in
      if not found then soft_failure (Failure "nothing to expand");      
      s
    in
    
    let tbl = S.table s in
    match Args.convert_as_lsymb [Args.Theory arg] with
    | Some m ->
      let m = Symbols.Macro.of_lsymb m tbl in
      expand targets (`Msymb m) s 

    | _ ->
      match convert_args s [Args.Theory arg] Args.(Sort Message) with
      | Args.Arg (Args.Message (f, _)) ->
        expand targets (`Mterm f) s 

      | _ ->
        hard_failure (Tactics.Failure "expected a message term")

  let expands (args : Theory.term list) (s : S.t) : S.t =
    List.fold_left (fun s arg -> expand_arg (target_all s) arg s) s args 

  let expand_tac args s =
    let args = List.map (function
        | Args.Theory t -> t
        | _ -> bad_args ()
      ) args
    in
    [expands args s]

  let expand_tac args = wrap_fail (expand_tac args)

  (*------------------------------------------------------------------*)
  (** {3 Rewriting types and functions} *)

  type rw_arg = 
    | Rw_rw of Ident.t option * rw_erule
    (* The ident is the ident of the hyp the rule came from (if any) *)

    | Rw_expand of Theory.term

  type rw_earg = Args.rw_count * rw_arg
  
  (** [rewrite ~all tgt rw_args] rewrites [rw_arg] in [tgt].
      If [all] is true, then does not fail if no rewriting occurs. *)
  let rewrite ~all 
      (targets: target list) 
      (rw : Args.rw_count * Ident.t option * rw_erule) 
      (s : S.sequent) 
    : S.sequent * S.sequent list 
    =
    let found1, cpt_occ = ref false, ref 0 in
    let check_max_rewriting () =
        if !cpt_occ > 1000 then   (* hard-coded *)
          hard_failure (Failure "max nested rewriting reached (1000)");
        incr cpt_occ;
        found1 := true;
    in

    let table, system = S.table s, S.system s in
    
    (* Attempt to find an instance of [left], and rewrites all occurrences of
       this instance.
       Return: (f, subs) *)
    let rec doit
      : type a. Args.rw_count -> a rw_rule -> cform -> cform * Term.form list = 
      fun mult (tyvars, sv, rsubs, left, right) f ->
        check_max_rewriting ();
        
        let subs_r = ref [] in
        let found_instance = ref false in
        
        (* This is a reference, so that it can be over-written later
           after we found an instance of [left]. *)
        let pat : a Term.term Match.pat ref = 
          ref Match.{ pat_tyvars = tyvars; pat_vars = sv; pat_term = left }
        in
        let right_instance = ref None in

        (* If there is a match (with [mv]), substitute [occ] by [right] where 
           free variables are instantiated according to [mv], and variables
           bound above the matched occurrences are universally quantified in 
           the generated sub-goals. *)
        let rw_inst (Term.ETerm occ) subst vars conds =
          match Match.T.try_match_term table system ~subst occ !pat with
          | NoMatch _ | FreeTyv -> `Continue

          (* head matches *)
          | Match mv ->
            if !found_instance then
              (* we already found the rewrite instance earlier *)
              `Map (oget !right_instance)
                
            else begin (* we found the rewrite instance *)
              found_instance := true;
              let subst = Match.Mvar.to_subst ~mode:`Match mv in
              let left = Term.subst subst left in
              let right = Term.subst subst right in

              right_instance := Some (Term.ETerm right);
              subs_r :=
                List.map (fun rsub ->
                    Term.mk_forall ~simpl:true vars (Term.subst subst rsub)
                  ) rsubs;

              pat := Match.{ pat_term   = left;
                             pat_tyvars = [];
                             pat_vars   = Sv.empty; };
              
              `Map (Term.ETerm right)
            end
        in

        let f_opt = match f with
          | `Equiv f -> 
            let f_opt = Match.E.map rw_inst (S.env s) f in
            omap (fun x -> `Equiv x) f_opt

          | `Reach f ->
            let f_opt = Match.T.map rw_inst (S.env s) f in
            omap (fun x -> `Reach x) f_opt
        in

        match mult, f_opt with
        | `Any, None -> f, !subs_r

        | (`Once | `Many), None -> 
          if not all 
          then soft_failure Tactics.NothingToRewrite 
          else f, !subs_r

        | (`Many | `Any), Some f -> 
          let f, rsubs' = doit `Any (tyvars, sv, rsubs, left, right) f in
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

    let doit_tgt (f,tgt_id : cform * Ident.t option) : cform * S.conc_form list =
      match rw with
      | mult,  id_opt, (tyvars, sv, subs, Term.ESubst (l,r)) ->
        if is_same id_opt tgt_id 
        then f, []
        else
          let f, subs = doit mult (tyvars, sv, subs, l, r) f in
          let subs = List.rev subs in
          f, List.map (fun l -> S.unwrap_conc (`Reach l)) subs
    in

    let s, subs = do_targets doit_tgt s targets in

    if all && not !found1 then soft_failure Tactics.NothingToRewrite;

    s, subs

  (** Parse rewrite tactic arguments as rewrite rules with possible subgoals 
      showing the rule validity. *)
  let p_rw_item (rw_arg : Args.rw_item) (s : S.t) : rw_earg * S.sequent list =
    let p_rw_rule dir (p_pt : Theory.p_pt_hol) :
      rw_erule * S.sequent list * Ident.t option = 
      let ghyp, pat = S.convert_pt_hol p_pt Equiv.Local_t s in
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

    | Rw_expand arg -> [expand_arg targets arg s]


  (*------------------------------------------------------------------*)
  (** {3 Case tactic} *)

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

    let cases = SystemExpr.map_descrs mk_case table system in

    List.map (fun (indices, ts_case) ->
        let ts_subst =
          if indices = [] then [Term.ESubst (ts, ts_case)] else []
        in
        let goal = S.subst_conc ts_subst (S.goal s) in
        let prem =
          S.Conc.mk_exists ~simpl:false indices
            (S.unwrap_conc (`Reach (Term.mk_atom `Eq ts ts_case)))
        in
        S.set_goal (S.Conc.mk_impl ~simpl:false prem goal) s
      ) cases

  (** Case analysis on disjunctions in an hypothesis.
      When [nb=`Any], recurses.
      When [nb=`Some l], destruct at most [l]. *)
  let hypothesis_case ~nb id (s : S.sequent) : c_res list =
    let destr_err () = soft_failure (Failure "not a disjunction") in

    let rec case acc form = match S.Hyp.destr_or form with
      | Some (f,g) -> case (case acc g) f
      | None       -> form :: acc in

    let form = Hyps.by_id id s in
    let s = Hyps.remove id s in

    let cases = match nb with
      | `Any -> case [] form
      | `Some l -> match S.Hyp.destr_ors l form with
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
  (** {3 Reduce} *)

  (** Reduce the full sequent *)
  let reduce_sequent param s =
    let mapper k f =
      S.reduce param s k f
    in
      S.map { call = mapper } s

  (** Reduce the goal *)
  let reduce_goal param s =
    S.set_goal (S.reduce param s S.conc_kind (S.goal s)) s

  let reduce_args args s : S.t list =
    match args with
    | [] -> [reduce_goal Reduction.rp_full s]
    | _ -> bad_args ()

  let reduce_tac args = wrap_fail (reduce_args args)

  (*------------------------------------------------------------------*)
  (** {3 Clear} *)

  let clear (hid : Ident.t) s = Hyps.remove hid s

  let clear_str (hyp_name : lsymb) s : S.t =
    let hid,_ = Hyps.by_name hyp_name s in
    clear hid s

  let clear_tac_args (args : Args.parser_arg list) s : S.t list =
    let s =
      List.fold_left (fun s arg -> match arg with
          | Args.String_name arg -> clear_str arg s
          | _ -> bad_args ()
        ) s args in
    [s]

  let clear_tac args = wrap_fail (clear_tac_args args)

  (*------------------------------------------------------------------*)
  (** {3 Revert} *)

  let revert (hid : Ident.t) (s : S.t) : S.t =
    let f = Hyps.by_id hid s in
    let f = S.hyp_to_conc f in
    let s = Hyps.remove hid s in
    S.set_goal (S.Conc.mk_impl ~simpl:false f (S.goal s)) s

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

  (*------------------------------------------------------------------*)
  (** {3 Intro patterns} *)

  let var_of_naming_pat 
      n_ip ~dflt_name (ty : 'a Type.ty) env : Vars.env * 'a Vars.var = 
    match n_ip with
    | Args.Unnamed
    | Args.AnyName     -> Vars.make `Approx env ty dflt_name
    | Args.Approx name -> Vars.make `Approx env ty name
    | Args.Named name  -> make_exact env ty name

  (*------------------------------------------------------------------*)
  (** Apply a naming pattern to a variable or hypothesis. *)
  let do_naming_pat (ip_handler : Args.ip_handler) n_ip s : S.t =
    match ip_handler with
    | `Var Vars.EVar v ->
      let env, v' = 
        var_of_naming_pat n_ip ~dflt_name:(Vars.name v) (Vars.ty v) (S.env s)
      in
      let subst = [Term.ESubst (Term.mk_var v, Term.mk_var v')] in

      (* FIXME: we substitute everywhere. This is inefficient. *)
      S.subst subst (S.set_env env s)

    | `Hyp hid ->
      let f = Hyps.by_id hid s in
      let s = Hyps.remove hid s in

      Hyps.add n_ip f s

  (*------------------------------------------------------------------*)
  (** Apply a And pattern (this is a destruct) of length [l].
      Note that variables in handlers have not been added to the env yet. *)
  let do_and_pat (hid : Ident.t) len s : Args.ip_handler list * S.t =
    let destr_fail s =
      soft_failure (Tactics.Failure ("cannot destruct: " ^ s))
    in
    
    let get_destr ~orig = function
      | Some x -> x
      | None -> destr_fail (Fmt.str "%a" Equiv.Any.pp orig)
    in

    assert (len > 0);
    if len = 1 then ([`Hyp hid], s) else
      let form = Hyps.by_id hid s in
      let s = Hyps.remove hid s in

      if S.Hyp.is_matom form then
        begin
          match S.Hyp.destr_matom form with
          | Some (`Eq,a,b) ->
            let a1, a2 = get_destr ~orig:(`Reach a) (Term.destr_pair a)
            and b1, b2 = get_destr ~orig:(`Reach b) (Term.destr_pair b) in

            let f1 = Term.mk_atom `Eq a1 b1
            and f2 = Term.mk_atom `Eq a2 b2 in

            let forms = 
              List.map (fun x -> Args.Unnamed, S.unwrap_hyp (`Reach x)) [f1;f2]
            in
            let ids, s = Hyps.add_i_list forms s in
            List.map (fun id -> `Hyp id) ids, s

          | _ -> destr_fail (Fmt.str "%a" S.pp_hyp form)
        end
        
      else if S.Hyp.is_and form then
        begin
          let ands = 
            get_destr ~orig:(S.wrap_hyp form) (S.Hyp.destr_ands len form)
          in
          let ands = List.map (fun x -> Args.Unnamed, x) ands in
          let ids, s = Hyps.add_i_list ands s in
          List.map (fun id -> `Hyp id) ids, s
        end

      else if S.Hyp.is_exists form then
        begin
          let vs, f = 
            get_destr ~orig:(S.wrap_hyp form) (S.Hyp.destr_exists form)
          in
          
          if List.length vs < len - 1 then
            hard_failure (Tactics.PatNumError (len - 1, List.length vs));
          
          let vs, vs' = List.takedrop (len - 1) vs in
          
          let vs_fresh, subst = Term.erefresh_vars `Global vs in
          
          let f = S.Hyp.mk_exists vs' f in
          let f = S.subst_hyp subst f in
          
          let idf, s = Hyps.add_i Args.Unnamed f s in
          
          ( (List.map (fun x -> `Var x) vs_fresh) @ [`Hyp idf], s )
        end

      else destr_fail (Fmt.str "%a" S.pp_hyp form)

  (** Apply an And/Or pattern to an ident hypothesis handler. *)
  let rec do_and_or_pat (hid : Ident.t) (pat : Args.and_or_pat) s
    : S.t list =
    match pat with
    | Args.And s_ip ->
      (* Destruct the hypothesis *)
      let handlers, s = do_and_pat hid (List.length s_ip) s in

      if List.length handlers <> List.length s_ip then
        hard_failure (Tactics.PatNumError (List.length s_ip, List.length handlers));

      (* Apply, for left to right, the simple patterns, and collect everything *)
      let ss = List.fold_left2 (fun ss handler ip ->
          List.map (do_simpl_pat handler ip) ss
          |> List.flatten
        ) [s] handlers s_ip in
      ss

    | Args.Or s_ip ->
      let ss = hypothesis_case ~nb:(`Some (List.length s_ip)) hid s in

      if List.length ss <> List.length s_ip then
        hard_failure (Tactics.PatNumError (List.length s_ip, List.length ss));

      (* For each case, apply the corresponding simple pattern *)
      List.map2 (fun (CHyp id, s) ip ->
          do_simpl_pat (`Hyp id) ip s
        ) ss s_ip

      (* Collect all cases *)
      |> List.flatten

    | Args.Split ->
      (* Destruct many Or *)
      let ss = hypothesis_case ~nb:`Any hid s in

      (* For each case, apply the corresponding simple pattern *)
      List.map (fun (CHyp id, s) ->
          revert id s
        ) ss

  (** Apply an simple pattern a handler. *)
  and do_simpl_pat (h : Args.ip_handler) (ip : Args.simpl_pat) s : S.t list =
    match h, ip with
    | _, Args.SNamed n_ip -> [do_naming_pat h n_ip s]

    | `Hyp id, Args.SAndOr ao_ip ->
      do_and_or_pat id ao_ip s

    | `Hyp id, Args.Srewrite dir ->
      let loc = L.loc dir in
      let f =
        Equiv.Babel.convert ~loc
          ~src:S.hyp_kind
          ~dst:Equiv.Local_t
          (Hyps.by_id id s)
      in
      let s = Hyps.remove id s in
      let pat = Match.pat_of_form f in
      let erule = Rewrite.pat_to_rw_erule ~loc (L.unloc dir) pat in
      let s, subgoals = rewrite ~all:false [T_conc] (`Many, Some id, erule) s in
      subgoals @ [s]

    | `Var _, (Args.SAndOr _ | Args.Srewrite _) ->
      hard_failure (Failure "intro pattern not applicable")


  (*------------------------------------------------------------------*)
  (** introduces the topmost variable of the goal. *)
  let rec do_intro_var (s : S.t) : Args.ip_handler * S.t =
    let form = S.goal s in

    if S.Conc.is_forall form then
      begin
        match S.Conc.decompose_forall form with
        | Vars.EVar x :: vs, f ->
          let x' = Vars.make_new_from x in

          let subst = [Term.ESubst (Term.mk_var x, Term.mk_var x')] in

          let f = S.Conc.mk_forall ~simpl:false vs f in

          let new_formula = S.subst_conc subst f in
          ( `Var (Vars.EVar x'),
            S.set_goal new_formula s )

        | [], f ->
          (* FIXME: this case should never happen. *)
          do_intro_var (S.set_goal f s)
      end

    else soft_failure Tactics.NothingToIntroduce

  (** Introduce the topmost element of the goal. *)
  let rec do_intro (s : S.t) : Args.ip_handler * S.t =
    let form = S.goal s in 
    if S.Conc.is_forall form then
      begin
        match S.Conc.decompose_forall form with
        | [], f ->
          (* FIXME: this case should never happen. *)
          do_intro (S.set_goal f s)

        | _ -> do_intro_var s
      end

    else if S.Conc.is_impl form then
      begin
        let lhs, rhs = oget (S.Conc.destr_impl form) in
        let lhs = S.hyp_of_conc lhs in
        let id, s = Hyps.add_i Args.Unnamed lhs s in
        let s = S.set_goal rhs s in
        `Hyp id, s
      end
      
    else if S.Conc.is_not form then
      begin
        let f = oget (S.Conc.destr_not form) in
        let f = S.hyp_of_conc f in
        let id, s = Hyps.add_i Args.Unnamed f s in
        let s = S.set_goal S.Conc.mk_false s in
        `Hyp id, s
      end

    else if S.Conc.is_matom form then
      begin
        match oget (S.Conc.destr_matom form) with
        | `Neq, u, v ->
          let h = Term.mk_atom `Eq u v in
          let h = S.unwrap_hyp (`Reach h) in
          let id, s = Hyps.add_i Args.Unnamed h s in
          let s = S.set_goal S.Conc.mk_false s in
          `Hyp id, s
        | _ -> soft_failure Tactics.NothingToIntroduce
      end
      
    else soft_failure Tactics.NothingToIntroduce

  let do_intro_pat (ip : Args.simpl_pat) s : S.t list =
    let handler, s = do_intro s in
    do_simpl_pat handler ip s

  (** Correponds to `intro *`, to use in automated tactics. *)
  let rec intro_all (s : S.t) : S.t list =
    try
      let s_ip = Args.(SNamed AnyName) in
      let ss = do_intro_pat s_ip s in
      List.concat_map intro_all ss

    with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]

  (*------------------------------------------------------------------*)
  let do_destruct hid s =
    (* Only destruct the top-most connective *)
    let handlers, s = do_and_pat hid 2 s in
    [List.fold_left (fun s handler ->
         (* TODO: location errors *)
         do_naming_pat handler Args.AnyName s
       ) s handlers]

  let destruct_tac_args args s =
    match args with
    | [Args.String_name h; Args.AndOrPat pat] ->
      let hid, _ = Hyps.by_name h s in
      do_and_or_pat hid pat s

    | [Args.String_name h] ->
      let hid, _ = Hyps.by_name h s in
      do_destruct hid s

    | _ -> bad_args ()

  let destruct_tac args = wrap_fail (destruct_tac_args args)

  (*------------------------------------------------------------------*)
  (** {3 Generalize} *)

  let try_clean_env vars s : S.t =
    let s_fv = S.fv s in
    let clear = Sv.diff vars (Sv.inter vars s_fv) in
    let env = Vars.rm_evars (S.env s) (Sv.elements clear) in
    S.set_env env s

  let _generalize ~dependent (Term.ETerm t) s : Vars.evar * S.t =
    let v = Vars.make_new (Term.ty t) "_x" in

    let subst = [Term.ESubst (t, Term.mk_var v)] in

    let s = 
      if not dependent 
      then S.set_goal (S.subst_conc subst (S.goal s)) s
      else S.subst subst s
    in

    let gen_hyps, s = 
      if not dependent 
      then [], s
      else
        Hyps.fold (fun id f (gen_hyps, s) ->
            if Vars.Sv.mem (Vars.EVar v) (S.fv_hyp f)
            then S.hyp_to_conc f :: gen_hyps, Hyps.remove id s
            else gen_hyps, s
          ) s ([], s)
    in

    let goal = S.Conc.mk_impls ~simpl:true gen_hyps (S.goal s) in
    Vars.EVar v, S.set_goal goal s

  (** [terms] and [n_ips] must be of the same length *)
  let generalize ~dependent terms n_ips s : S.t = 
    let s, vars = 
      List.fold_right (fun term (s, vars) ->
          let var, s = _generalize ~dependent term s in
          s, var :: vars
        ) terms (s,[])
    in

    (* clear unused variables among [terms] free variables *)
    let t_fv = 
      List.fold_left (fun vars (Term.ETerm t) -> 
          Sv.union vars (Term.fv t)
        ) Sv.empty terms 
    in
    let s = try_clean_env t_fv s in

    (* we rename generalized variables *)
    let _, new_vars, subst = 
      List.fold_left2 (fun (env, new_vars, subst) (Vars.EVar v) n_ip ->
          let env, v' = 
            var_of_naming_pat n_ip ~dflt_name:"x" (Vars.ty v) env 
          in
          env, 
          Vars.EVar v' :: new_vars,
          Term.ESubst (Term.mk_var v, Term.mk_var v') :: subst
        ) (S.env s, [], []) vars n_ips
    in
    let s = S.subst subst s in

    (* quantify universally *)
    let new_vars = List.rev new_vars in
    let goal = S.Conc.mk_forall ~simpl:false new_vars (S.goal s) in
    S.set_goal goal s 

  let naming_pat_of_eterm (Term.ETerm t) =
    match t with
    | Term.Var v -> Args.Approx (Vars.name v) (* use the same name *)
    | _ -> Args.AnyName

  let generalize_tac_args ~dependent args s : S.t list =
    match args with
    | [Args.Generalize (terms, n_ips_opt)] ->
      let terms =
        List.map (fun arg ->
            match convert_args s [Args.Theory arg] (Args.Sort Args.ETerm) with
            | Args.Arg (Args.ETerm (_, t, _)) -> Term.ETerm t

            | _ -> bad_args ()
          ) terms
      in
      let n_ips = 
        match n_ips_opt with 
        | None -> List.map naming_pat_of_eterm terms
        | Some n_ips ->
          if List.length n_ips <> List.length terms then
            hard_failure (Failure "not the same number of arguments \
                                   and naming patterns");
          n_ips
      in

      [generalize ~dependent terms n_ips s]

    | _ -> assert false

  let generalize_tac ~dependent args = 
    wrap_fail (generalize_tac_args ~dependent args)


  (*------------------------------------------------------------------*)
  (** {3 Apply}
    *
    * In local and global sequents, we can apply an hypothesis
    * to derive the goal or to derive the conclusion of an hypothesis.
    * The former corresponds to [apply] below and the latter corresponds
    * to [apply_in].
    *
    * We impose in both that the hypotheses involved here are of the same
    * kind as conclusion formulas: this is immediate for global sequents
    * and, in the case of local sequents, means that we only consider
    * local hypotheses. This might be generalized later, or complemented
    * with other tactics that would have to generate global sequents
    * as premisses. *)

  let apply (pat : S.conc_form Match.pat) (s : S.t) : S.t list =
    let subs, f = S.Conc.decompose_impls_last pat.pat_term in

    if not (Vars.Sv.subset pat.pat_vars (S.fv_conc f)) then
      soft_failure ApplyBadInst;

    let pat = { pat with pat_term = f } in

    (* Check that [pat] entails [S.goal s]. *)
    match S.MatchF.try_match ~mode:`EntailRL 
            (S.table s) (S.system s) 
            (S.goal s) pat 
    with
    | NoMatch minfos  -> soft_failure (ApplyMatchFailure minfos)
    | FreeTyv         -> soft_failure (ApplyMatchFailure None)
    | Match mv ->
      let subst = Match.Mvar.to_subst ~mode:`Match mv in

      let goals = List.map (S.subst_conc subst) subs in
      List.map (fun g -> S.set_goal g s) goals

  (** [apply_in f hyp s] tries to match a premise of [f] with the conclusion of
      [hyp], and replaces [hyp] by the conclusion of [f].
      It generates a new subgoal for any remaining premises of [f], plus all
      premises of the original [hyp].

      E.g., if `H1 : A -> B` and `H2 : A` then `apply H1 in H2` replaces
      `H2 : A` by `H2 : B`. *)
  let apply_in (pat : S.conc_form Match.pat) (hyp : Ident.t) (s : S.t)
    : S.t list =
    let fprems, fconcl = S.Conc.decompose_impls_last pat.pat_term in

    let h = Hyps.by_id hyp s in
    let h = S.hyp_to_conc h in
    let hprems, hconcl = S.Conc.decompose_impls_last h in

    let try1 (fprem : S.conc_form) =
      if not (Vars.Sv.subset pat.pat_vars (S.fv_conc fprem)) then None
      else
        let pat = { pat with pat_term = fprem } in

        (* Check that [hconcl] entails [pat]. *)
        match
          S.MatchF.try_match ~mode:`EntailLR (S.table s) (S.system s) hconcl pat 
        with
        | NoMatch _ | FreeTyv -> None
        | Match mv -> Some mv
    in

    (* try to match a premise of [form] with [hconcl] *)
    let rec find_match acc fprems = match fprems with
      | [] -> None
      | fprem :: fprems ->
        match try1 fprem with
        | None -> find_match (fprem :: acc) fprems
        | Some mv ->
          (* premises of [form], minus the matched premise *)
          let fprems_other = List.rev_append acc fprems in
          Some (fprems_other, mv)
    in

    match find_match [] fprems with
    | None -> soft_failure (ApplyMatchFailure None)
    | Some (fsubgoals,mv) ->
      let subst = Match.Mvar.to_subst ~mode:`Match mv in

      (* instantiate the inferred variables everywhere *)
      let fprems_other = List.map (S.subst_conc subst) fsubgoals in
      let fconcl = S.subst_conc subst fconcl in

      let goal1 =
        let s = Hyps.remove hyp s in
        Hyps.add (Args.Named (Ident.name hyp)) (S.hyp_of_conc fconcl) s
      in

      List.map
        (fun prem ->
           S.set_goal prem s)
        (hprems @               (* remaining premises of [hyp] *)
         fprems_other)          (* remaining premises of [form] *)
      @
      [goal1]


  (** Parse apply tactic arguments. *)
  let p_apply_args (args : Args.parser_arg list) (s : S.sequent) :
    S.t list * S.conc_form Match.pat * target =
    let subgoals, pat, in_opt =
      match args with
      | [Args.ApplyIn (Theory.PT_hol pt,in_opt)] ->
        let _, pat = S.convert_pt_hol pt S.conc_kind s in
        [], pat, in_opt

      (* | [Args.ApplyIn (Theory.PT_form f,in_opt)] ->
       *   begin
       *     match convert_args s args Args.(Sort Boolean) with
       *     | Args.Arg (Boolean f) ->
       *       let subgoal = S.set_goal f s in
       *       let pat = Term.pat_of_form f in
       *       [subgoal], pat, in_opt
       * 
       *     | _ -> bad_args ()
       *   end *)

      | _ -> bad_args ()
    in

    let target = match in_opt with
      | Some lsymb -> T_hyp (fst (Hyps.by_name lsymb s))
      | None       -> T_conc
    in
    subgoals, pat, target


  let apply_tac_args (args : Args.parser_arg list) s : S.t list =
    let subgoals, pat, target = p_apply_args args s in
    match target with
    | T_conc    -> subgoals @ apply pat s
    | T_hyp id  -> subgoals @ apply_in pat id s 
    | T_felem _ -> assert false

  let apply_tac args = wrap_fail (apply_tac_args args)

  (*------------------------------------------------------------------*)
  (** {3 Induction} *)
  
  let induction s =
    let error () =
      soft_failure
        (Failure "conclusion must be an universal quantification \
                  over a timestamp")
    in

    let goal = S.goal s in
    let vs0, f = S.Conc.decompose_forall goal in
    let Vars.EVar v, vs = match vs0 with
      | v :: vs -> v, vs
      | _ -> error ()
    in

    match Vars.ty v with
    | Type.Timestamp ->
      begin
        let env = Vars.of_list vs0 in
        let _,v' = Vars.fresh env v in

        let ih =
          let atom_lt =
            Equiv.Babel.convert
              ~dst:S.conc_kind
              ~src:Equiv.Local_t
              (Term.mk_atom `Lt (Term.mk_var v') (Term.mk_var v))
          in
          
          S.Conc.mk_forall ~simpl:false
            (Vars.EVar v' :: vs)
            (S.Conc.mk_impl ~simpl:false
               (atom_lt) 
               (S.subst_conc [Term.ESubst (Term.mk_var v,Term.mk_var v')] f))
        in

        let new_goal = 
          S.Conc.mk_forall ~simpl:false
            [Vars.EVar v]
            (S.Conc.mk_impl ~simpl:false
               ih
               (S.Conc.mk_forall ~simpl:false vs f))
        in

        [S.set_goal new_goal s]
      end
    | _ -> error ()

  let induction_gen ~dependent (t : Term.timestamp) s : S.t list =
    let t = Term.ETerm t in
    let s = generalize ~dependent [t] [naming_pat_of_eterm t] s in
    induction s

  let induction_args ~dependent args s = 
    match args with
    | [] -> induction s
    | [Args.Theory t] -> 
      begin
        match convert_args s args (Args.Sort Args.Timestamp) with
        | Args.Arg (Args.Timestamp t) -> induction_gen ~dependent t s
        | _ -> hard_failure (Failure "expected a timestamp")
      end
    | _ -> bad_args ()

  let induction_tac ~dependent args = 
    wrap_fail (induction_args ~dependent args)

  (*------------------------------------------------------------------*)
  (** {3 Exists} *)

  (** [goal_exists_intro judge ths] introduces the existentially
      quantified variables in the conclusion of the judgment,
      using [ths] as existential witnesses. *)
  let goal_exists_intro  ths (s : S.t) =
    let vs, f = S.Conc.decompose_exists (S.goal s) in

    if not (List.length ths = List.length vs) then
      soft_failure (Tactics.Failure "cannot introduce exists");

    let table = S.table s in
    let nu = Theory.parse_subst table (S.ty_vars s) (S.env s) vs ths in
    let new_formula = S.subst_conc nu f in
    [S.set_goal new_formula s]

  let exists_intro_args args s =
    let args = 
      List.map (function
          | Args.Theory tm -> tm
          | _ -> bad_args ()
        ) args 
    in
    goal_exists_intro args s 

  let exists_intro_tac args = wrap_fail (exists_intro_args args)

  (*------------------------------------------------------------------*)
  (** {3 Use} *)

  (** [use ip name ths judge] applies the formula named [gp],
    * eliminating its universally quantified variables using [ths],
    * and eliminating implications (and negations) underneath.
    * If given an introduction patterns, apply it to the generated hypothesis.
    * As with apply, we require that the hypothesis (or lemma) is
    * of the kind of conclusion formulas: for local sequents this means
    * that we cannot use a global hypothesis or lemma. *)
  let use ip (name : lsymb) (ths : Theory.term list) (s : S.t) =
    (* Get formula to apply. *)
    let stmt = S.get_assumption S.conc_kind name s in

    (* FIXME *)
    if stmt.ty_vars <> [] then
      soft_failure (Failure "free type variables not supported with \
                             use tactic") ;

    (* Get universally quantified variables, verify that lengths match. *)
    let uvars,f = S.Conc.decompose_forall stmt.formula in

    if List.length uvars < List.length ths then
      Tactics.(soft_failure (Failure "too many arguments")) ;

    let uvars, uvars0 = List.takedrop (List.length ths) uvars in
    let f = S.Conc.mk_forall ~simpl:false uvars0 f in

    (* refresh *)
    let uvars, subst = Term.erefresh_vars `Global uvars in
    let f = S.subst_conc subst f in

    let subst = 
      Theory.parse_subst (S.table s) (S.ty_vars s) (S.env s) uvars ths 
    in

    (* instantiate [f] *)
    let f = S.subst_conc subst f in

    (* Compute subgoals by introducing implications on the left. *)
    let rec aux subgoals form = 
      if S.Conc.is_impl form then
        begin
          let h, c = oget (S.Conc.destr_impl form) in
          let s' = S.set_goal h s in
          aux (s'::subgoals) c
        end

      else if S.Conc.is_not form then
        begin
          let h = oget (S.Conc.destr_not form) in
          let s' = S.set_goal h s in
          List.rev (s'::subgoals)
        end

      else
        begin
          let idf, s0 = Hyps.add_i Args.AnyName (S.hyp_of_conc form) s in
          let s0 = match ip with
            | None -> [s0]
            | Some ip -> do_simpl_pat (`Hyp idf) ip s0 in
          s0 @ List.rev subgoals
        end
    in

    aux [] f

  let use_args args s =
    let ip, args = match args with
      | Args.SimplPat ip :: args -> Some ip, args
      | args                     -> None, args in
    match args with
    | Args.String_name id :: th_terms ->
      let th_terms =
        List.map
          (function
            | Args.Theory th -> th
            | _ -> bad_args ())
          th_terms
      in
      use ip id th_terms s 
    | _ -> bad_args ()

  let use_tac args = wrap_fail (use_args args)

  (*------------------------------------------------------------------*)
  (** {3 Assert} *)

  (** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
    * to be proved, and the other where [f] is assumed.
    * We only consider the case here where [f] is a local formula
    * (which is then converted to conclusion and hypothesis formulae)
    * more general forms should be allowed here or elsewhere. *)
  let my_assert (args : Args.parser_arg list) s : S.t list =
    let ip, f = match args with
      | [f] -> None, f
      | [f; Args.SimplPat ip] -> Some ip, f
      | _ -> bad_args () in

    let f = match convert_args s [f] Args.(Sort Boolean) with
      | Args.(Arg (Boolean f)) -> f
      | _ -> bad_args () 
    in
    let f_conc =
      Equiv.Babel.convert f ~src:Equiv.Local_t ~dst:S.conc_kind in
    let f_hyp =
      Equiv.Babel.convert f ~src:Equiv.Local_t ~dst:S.hyp_kind in

    let s1 = S.set_goal f_conc s in
    let id, s2 = Hyps.add_i Args.AnyName f_hyp s in
    let s2 = match ip with
      | Some ip -> do_simpl_pat (`Hyp id) ip s2
      | None -> [s2] 
    in
    s1 :: s2

  let assert_tac args = wrap_fail (my_assert args)


  (*------------------------------------------------------------------*)
  (** {3 Depends} *)

  let depends Args.(Pair (Timestamp a1, Timestamp a2)) s =
    match a1, a2 with
    | Term.Action(n1, is1), Term.Action (n2, is2) ->
      let table = S.table s in
      if Action.(depends (of_term n1 is1 table) (of_term n2 is2 table)) then
        let atom =
          Equiv.Babel.convert
            (Term.mk_atom `Lt a1 a2)
            ~src:Equiv.Local_t ~dst:S.conc_kind in
        let g = S.Conc.mk_impl ~simpl:false atom (S.goal s) in
        [happens_premise s a2;
         S.set_goal g s]

      else
        soft_failure
          (Tactics.NotDepends (Fmt.strf "%a" Term.pp a1,
                               Fmt.strf "%a" Term.pp a2))
          
    | _ -> soft_failure (Tactics.Failure "arguments must be actions")

  (*------------------------------------------------------------------*)
  (** {3 Remember} *)

  let remember (id : Theory.lsymb) (term : Theory.term) s =
    match econvert s term with
    | None -> soft_failure ~loc:(L.loc term) (Failure "type error")
    | Some (Theory.ETerm (ty, t, _)) ->
      let env, x = make_exact ~loc:(L.loc id) (S.env s) ty (L.unloc id) in
      let subst = [Term.ESubst (t, Term.mk_var x)] in

      let s = S.subst subst (S.set_env env s) in
      let eq =
        Equiv.Babel.convert
          (Term.mk_atom `Eq (Term.mk_var x) t)
          ~src:Equiv.Local_t ~dst:S.conc_kind in
      S.set_goal (S.Conc.mk_impl ~simpl:false eq (S.goal s)) s

  let remember_tac_args (args : Args.parser_arg list) s : S.t list =
    match args with
    | [Args.Remember (term, id)] -> [remember id term s]
    | _ -> bad_args ()

  let remember_tac args = wrap_fail (remember_tac_args args)

  (*------------------------------------------------------------------*)
  (** {3 Rewrite} *)

  type f_simpl = strong:bool -> close:bool -> S.t Tactics.tac

  let do_s_item (simpl : f_simpl) (s_item : Args.s_item) s : S.t list =
    match s_item with
    | Args.Simplify l ->
      let tac = simpl ~strong:true ~close:false in
      Tactics.run tac s

    | Args.Tryauto l ->
      let tac = Tactics.try_tac (simpl ~strong:true ~close:true) in
      Tactics.run tac s

    | Args.Tryautosimpl l ->
      let tac = 
        Tactics.andthen         (* FIXME: inneficient *)
          (Tactics.try_tac (simpl ~strong:true ~close:true))
          (simpl ~strong:true ~close:false)
      in
      Tactics.run tac s

  (** Applies a rewrite arg  *)
  let do_rw_arg (simpl : f_simpl) rw_arg rw_in s : S.t list =
    match rw_arg with
    | Args.R_item rw_item  -> 
      do_rw_item rw_item rw_in s
    | Args.R_s_item s_item -> 
      do_s_item simpl s_item s (* targets are ignored there *)

  let rewrite_tac (simpl : f_simpl) args s =
    match args with
    | [Args.RewriteIn (rw_args, in_opt)] ->
      List.fold_left (fun seqs rw_arg ->
          List.concat_map (do_rw_arg simpl rw_arg in_opt) seqs
        ) [s] rw_args

    | _ -> bad_args ()

  let rewrite_tac (simpl : f_simpl) args = wrap_fail (rewrite_tac simpl args)

  (*------------------------------------------------------------------*)
  (** {3 Intro} *)

  let rec do_intros_ip (simpl : f_simpl) (intros : Args.intro_pattern list) s =
    match intros with
    | [] -> [s]

    | (Args.SItem s_item) :: intros ->
      do_intros_ip_list simpl intros (do_s_item simpl s_item s)

    | (Args.Simpl s_ip) :: intros ->
      let ss = do_intro_pat s_ip s in
      do_intros_ip_list simpl intros ss

    | (Args.SExpnd s_e) :: intros ->
      let ss = do_rw_item (s_e :> Args.rw_item) `Goal s in
      let ss = as_seq1 ss in (* we get exactly one new goal *)
      do_intros_ip simpl intros ss

    | (Args.StarV loc) :: intros0 ->
      let repeat, s =
        try
          let handler, s = do_intro_var s in
          true, do_naming_pat handler Args.AnyName s

        with Tactics.Tactic_soft_failure (_,NothingToIntroduce) ->
          false, s
      in
      let intros = if repeat then intros else intros0 in
      do_intros_ip simpl intros s

    | (Args.Star loc) :: intros ->
      try
        let handler, s = do_intro s in
        let s = do_naming_pat handler Args.AnyName s in
        do_intros_ip simpl [Args.Star loc] s

      with Tactics.Tactic_soft_failure (_,NothingToIntroduce) -> [s]


  and do_intros_ip_list (simpl : f_simpl) intros ss = 
    List.concat_map (do_intros_ip simpl intros) ss

  let intro_tac_args (simpl : f_simpl) args s =
    match args with
    | [Args.IntroPat intros] -> do_intros_ip simpl intros s
    | _ -> bad_args ()

  let intro_tac (simpl : f_simpl) args = wrap_fail (intro_tac_args simpl args)

end
