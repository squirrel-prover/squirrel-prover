open Utils

module Args = HighTacticsArgs
module L = Location

module T = Prover.ProverTactics

module SE = SystemExpr

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
(** {3 Miscellaneous} *)

let bad_args () = hard_failure (Failure "improper arguments")

(*------------------------------------------------------------------*)
let check_ty_eq ?loc ty1 ty2 =
  if not (Type.equal ty1 ty2) then
    soft_failure ?loc
      (Failure (Fmt.str "types %a and %a are not compatible"
                  Type.pp ty1 Type.pp ty2));
  ()

(*------------------------------------------------------------------*)
let check_hty_eq ?loc hty1 hty2 =
  if not (Type.ht_equal hty1 hty2) then
    soft_failure ?loc
      (Failure (Fmt.str "types %a and %a are not compatible"
                  Type.pp_ht hty1 Type.pp_ht hty2));
  ()

(*------------------------------------------------------------------*)
(** {2 Functor building common tactics code from a Sequent module} *)

module MkCommonLowTac (S : Sequent.S) = struct

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

  (** build a pattern from a rewriting rule using S.Reduce to get the equality *)
  let pat_to_rw_rule s =
    Rewrite.pat_to_rw_rule
      ~destr_eq:(S.Reduce.destr_eq s Equiv.Local_t)

  (*------------------------------------------------------------------*)
  let wrap_fail f (s: S.sequent) sk fk =
    try sk (f s) fk with
    | Tactics.Tactic_soft_failure e -> fk e

  (*------------------------------------------------------------------*)
  let make_exact ?loc env ty name =
    match Vars.make_exact env ty name with
    | None ->
      hard_failure ?loc
        (Tactics.Failure ("variable name " ^ name ^ " already used"))
    | Some v' -> v'

  (*------------------------------------------------------------------*)
  let happens_premise (s : S.t) (a : Term.term) : S.t =
    let form = Term.mk_happens a in
    S.set_goal (S.unwrap_conc (`Reach form)) s

  (*------------------------------------------------------------------*)
  (** {3 Conversion} *)

  let convert_args (s : S.sequent) args sort =
    Args.convert_args (S.env s) args sort (S.wrap_conc (S.goal s))

  let convert (s : S.sequent) term =
    let cenv = Theory.{ env = S.env s; cntxt = InGoal; } in
    Theory.convert cenv term

  let convert_ht (s : S.sequent)  ht =
    let conv_env = Theory.{ env = S.env s; cntxt = InGoal; } in
    Theory.convert_ht conv_env ht

  (*------------------------------------------------------------------*)
  (** {3 Targets} *)

  type target =
    | T_conc              (** Conclusion. *)
    | T_hyp   of Ident.t  (** Hypothesis. *)
    | T_felem of int      (** Element in conclusion biframe. *)

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
      (doit : (
          (Equiv.any_form * Ident.t option) ->
          (Equiv.any_form * (SE.context * S.conc_form) list)))
      (s : S.sequent) (t : target)
    : S.sequent * S.sequent list
    =
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
      List.map
        (fun (sub_system, sub) -> S.set_goal_in_context sub_system sub s)
        subs
    in

    match t, f with
    | T_conc, f -> S.set_goal (S.unwrap_conc f) s, subs
    | T_hyp id, f ->
      Hyps.add (Args.Named (Ident.name id)) (S.unwrap_hyp f) s, subs
    | T_felem i, `Reach f -> S.change_felem i [f] s, subs
    | _ -> assert false

  let do_targets doit (s : S.sequent) (targets : target list)
    : S.sequent * S.sequent list
    =
    let s, subs =
      List.fold_left (fun (s,subs) target ->
          let s, subs' = do_target doit s target in
          s, List.rev_append subs' subs
        ) (s,[]) targets
    in
    s, List.rev subs


  (*------------------------------------------------------------------*)
  (** {3 Macro and term unfolding} *)

  (** [unfold_term_exn t se s] unfolds [t] w.r.t. the system [se].
      The sequent [s] is used to discharge Happens subgoals.
      If [se] is not a [SE.fset], the unfolding fail by raising an exception.*)
  let unfold_term_exn
      ?(mode : Macros.expand_context option)
      ?(force_happens=false)
      (t     : Term.term)
      (se    : SE.arbitrary)
      (s     : S.sequent)
    : Term.term
    =
    let se =
      if SE.is_fset se then SE.to_fset se
      else soft_failure
          (Tactics.Failure "nothing to expand: the system is too general")
    in

    match t with
    | Macro (ms,l,a) ->
      if not (force_happens) && not (S.query_happens ~precise:true s a) then
        soft_failure (Tactics.MustHappen a);

      Macros.get_definition_exn ?mode (S.mk_trace_cntxt ~se s) ms a 

    | Fun (fs, _, ts)
      when Operator.is_operator (S.table s) fs ->
      Operator.unfold (S.mk_trace_cntxt ~se s) fs ts

    | _ ->
      soft_failure (Tactics.Failure "nothing to expand")

  (** If [strict] is true, the unfolding must succeed. *)
  let unfold_term
      ?(mode : Macros.expand_context option)
      ?(force_happens=false)
      ~(strict:bool)
      (t     : Term.term)
      (se    : SE.arbitrary)
      (s     : S.sequent)
    : Term.term option
    =
    try Some (unfold_term_exn ~force_happens ?mode t se s) with
    | Tactics.Tactic_soft_failure _ when not strict -> None

  let found_occ_macro target ms occ =
    match target with
    | `Msymb mname -> ms.Term.s_symb = mname
    | `Mterm t     -> occ = t
    | `Any         -> true
    | `Fsymb _     -> false

  let found_occ_fun target fs =
    match target with
    | `Any                -> true
    | `Fsymb fname        -> fs = fname
    | `Msymb _ | `Mterm _ -> false

  type expand_kind = [
    | `Msymb of Symbols.macro
    | `Fsymb of Symbols.fname
    | `Mterm of Term.term
    | `Any
  ]

  let expand_term
      ?(m_rec = false)
      ~(mode : Macros.expand_context)
      (target : expand_kind)
      (s : S.sequent)
      (f : Equiv.any_form) : bool * Equiv.any_form
    =
    let found1 = ref false in

    (* unfold_macro is not allowed to fail if we try to expand a
       specific term *)
    let strict =
      match target with
      | `Mterm _ -> true
      | `Fsymb _ | `Msymb _ | `Any -> false
    in
    let unfold (se : SE.arbitrary) occ s =
      match unfold_term ~mode ~strict occ se s with
      | None -> `Continue
      | Some t ->
        found1 := true;
        `Map t
    in

    let expand_inst : Match.Pos.f_map =
      fun occ se _vars conds _p ->
        let s =                 (* adds [conds] in [s] *)
          List.fold_left (fun s cond ->
              S.Hyps.add AnyName (S.unwrap_hyp (`Reach cond)) s
            ) s conds
        in
        match occ with
        | Term.Macro (ms, _, _) ->
          if found_occ_macro target ms occ then
            unfold se occ s
          else
            `Continue

        | Term.Fun ((f,_), _, _) ->
          if found_occ_fun target f then
            unfold se occ s
          else
            `Continue

        | _ -> `Continue
    in

    match f with
    | `Equiv f ->
      let _, f =
        Match.Pos.map_e
          ~mode:(`TopDown m_rec) expand_inst (S.vars s) (S.system s) f
      in
      !found1, `Equiv f

    | `Reach f ->
      let _, f =
        Match.Pos.map
          ~mode:(`TopDown m_rec) expand_inst (S.vars s) (S.system s).set f
      in
      !found1, `Reach f


  (** If [m_rec = true], recurse on expanded sub-terms. *)
  let expand
      ?(m_rec = false)
      (targets: target list)
      (target : expand_kind)
      (s : S.sequent) : bool * S.sequent
    =
    let found1 = ref false in

    (* applies [doit] to all subterms of the target [f] *)
    let doit
        ((f,_) : Equiv.any_form * Ident.t option)
      : Equiv.any_form * (SE.context * S.conc_form) list
      =
      let found1', f = expand_term ~mode:Macros.InSequent ~m_rec target s f in
      found1 := found1' || !found1;
      f, []
    in

    let s, subs = do_targets doit s targets in
    assert (subs = []);

    !found1, s

  (** expand all macros (not operators) in a term relatively to a system *)
  let expand_all_macros
      ?(force_happens=false)
      (f : Term.term)
      (sexpr : SE.arbitrary)
      (s : S.t)
    : Term.term
    =
    let expand_inst : Match.Pos.f_map =
      fun (occ : Term.term) se _vars conds _p ->
        match occ with
        | Term.Macro (ms, l, _) ->
          begin
            let s =             (* add [conds] in [s] *)
              List.fold_left (fun s cond ->
                  S.Hyps.add AnyName (S.unwrap_hyp (`Reach cond)) s
                ) s conds
            in
            match
              unfold_term ~strict:false ~force_happens occ se s
            with
            | None -> `Continue
            | Some t -> `Map t
          end

        | _ -> `Continue
    in
    let _, f =
      Match.Pos.map
        ~mode:(`TopDown true) expand_inst (S.vars s) sexpr f
    in
    f

  (** expand all macro of some targets in a sequent *)
  let expand_all targets (s : S.sequent) : S.sequent =
    let _, s = expand ~m_rec:true targets `Any s in
    s

  (** exported *)
  let expand_all_l targets s : S.sequent list =
    let targets, _all = make_in_targets targets s in
    [expand_all targets s]

  (** parse a expand argument *)
  let p_rw_expand_arg (s : S.t) (arg : Theory.term) : expand_kind =
    let tbl = S.table s in
    match Args.convert_as_lsymb [Args.Theory arg] with
    | Some m ->
      if Symbols.Macro.mem m tbl then
        `Msymb (Symbols.Macro.of_lsymb m tbl)
      else if Symbols.Function.mem m tbl then
        `Fsymb (Symbols.Function.of_lsymb m tbl)
      else
        soft_failure ~loc:(L.loc arg) (Failure "not a macro or operator");

    | _ ->
      match convert_args s [Args.Theory arg] Args.(Sort Message) with
      | Args.Arg (Args.Message (f, _)) -> `Mterm f

      | _ ->
        hard_failure ~loc:(L.loc arg)
          (Tactics.Failure "expected a term of sort message")

  let expand_arg (targets : target list) (arg : Theory.term) (s : S.t) : S.t =
    let expnd_arg = p_rw_expand_arg s arg in
    let found, s = expand targets expnd_arg s in
    if not found then
      soft_failure ~loc:(L.loc arg) (Failure "nothing to expand");
    s

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
  (** {3 Print} *)

  let print_messages args s =
    let messages = List.map (fun arg ->
        match convert_args s [Args.Theory arg] Args.(Sort Message) with
        | Args.Arg (Args.Message (f, _)) -> f
        | _ ->
          hard_failure ~loc:(L.loc arg)
            (Tactics.Failure "expected a term of sort message")
      ) args in
    let pp_messages ppf messages = List.iteri
        (fun i m -> Fmt.pf ppf "@.%i:%a@." i Term.pp m)
        messages in
    Printer.prt `Result "%a" pp_messages messages;
    s

  let print_messages_tac args s =
    let args = List.map (function
        | Args.Theory t -> t
        | _ -> bad_args ()
      ) args
    in
    [print_messages args s]

  let print_messages_tac args = wrap_fail (print_messages_tac args)

  (*------------------------------------------------------------------*)
  (** {3 Rewriting types and functions} *)

  type rw_arg =
    | Rw_rw of L.t * Ident.t option * Rewrite.rw_rule
    (** The ident is the ident of the hyp the rule came from (if any) *)

    | Rw_expand    of Theory.term
    | Rw_expandall of Location.t

  type rw_earg = Args.rw_count * rw_arg

  let hyp_is_same (hyp_id : Ident.t option) (target_id : Ident.t option) =
    match hyp_id, target_id with
    | None, _ | _, None -> false
    | Some hyp_id, Some target_id ->
      Ident.name hyp_id = Ident.name target_id &&
      Ident.name hyp_id <> "_"

  (** [rewrite ~all tgt rw_args] rewrites [rw_arg] in [tgt].
      If [all] is true, then does not fail if no rewriting occurs. *)
  let rewrite
      ~(loc : L.t)
      ~(all : bool)
      (targets : target list)
      (rw : Args.rw_count * Ident.t option * Rewrite.rw_rule)
      (s : S.sequent)
    : S.sequent * S.sequent list
    =
    (* set to true if at least one rewriting occured in any of the targets *)
    let found = ref false in

    let mult, id_opt, rw_erule = rw in

    let doit_tgt
        (f,tgt_id : Equiv.any_form * Ident.t option)
      : Equiv.any_form * (SE.context * S.conc_form) list
      =
      if hyp_is_same id_opt tgt_id
      then f, []
      else
        match
          Rewrite.rewrite_exn
            ~loc (S.table s) (S.system s) InSequent
            (S.vars s) (S.get_trace_hyps s)
            mult rw_erule f
        with
        | f, subs ->
          found := true;
          f, List.map (fun (se, l) -> se, S.unwrap_conc (`Reach l)) subs

        | exception Tactics.Tactic_soft_failure (_,NothingToRewrite) ->
          if all then f, []
          else soft_failure ~loc Tactics.NothingToRewrite
    in

    let s, subs = do_targets doit_tgt s targets in

    if all && not !found then soft_failure ~loc Tactics.NothingToRewrite;

    s, subs

  (** Parse rewrite tactic arguments as rewrite rules. *)
  let p_rw_item (rw_arg : Args.rw_item) (s : S.t) : rw_earg =
    let p_rw_rule dir (p_pt : Theory.p_pt) : Rewrite.rw_rule * Ident.t option =
      let ghyp, pat_system, pat =
        S.convert_pt_gen
          ~check_compatibility:false
          ~close_pats:false
          p_pt Equiv.Local_t s
      in
      let id_opt = match ghyp with `Hyp id -> Some id | _ -> None in

      pat_to_rw_rule s pat_system.set dir pat, id_opt
    in

    let p_rw_item (rw_arg : Args.rw_item) : rw_earg =
      let rw = match rw_arg.rw_type with
        | `Rw f ->
          let dir = L.unloc rw_arg.rw_dir in
          (* (rewrite rule, subgols, hyp id) if applicable *)
          let rule, id_opt = p_rw_rule dir f in
          Rw_rw (f.p_pt_loc, id_opt, rule)

        | `Expand t ->
          if L.unloc rw_arg.rw_dir <> `LeftToRight then
            hard_failure ~loc:(L.loc rw_arg.rw_dir)
              (Failure "expand cannot take a direction");

          Rw_expand t

        | `ExpandAll loc -> Rw_expandall loc

      in
      rw_arg.rw_mult, rw
    in

    p_rw_item rw_arg

  (** Applies a rewrite item *)
  let do_rw_item
      (rw_item : Args.rw_item)
      (rw_in : Args.in_target)
      (s : S.sequent) : S.sequent list
    =
    let targets, all = make_in_targets rw_in s in
    let rw_c,rw_arg = p_rw_item rw_item s in

    match rw_arg with
    | Rw_rw (loc, id, erule) ->
      let s, subs = rewrite ~loc ~all targets (rw_c, id, erule) s in
      subs @                      (* prove instances premisses *)
      [s]                         (* final sequent *)

    | Rw_expand arg -> [expand_arg targets arg s]

    | Rw_expandall _ -> [expand_all targets s]

  (*------------------------------------------------------------------*)
  (** {3 Rewrite Equiv} *)

  (** Parameter for "rewrite equiv" tactic:
      - a global formula that is a chain of implications concluding
        with an equivalence atom;
      - the corresponding system expression;
      - the rewriting direction.
      The rewrite equiv tactic corresponds to the ReachEquiv rule of CSF'22. *)
  type rw_equiv =
    SystemExpr.context * Equiv.global_form * [ `LeftToRight | `RightToLeft ]

  (** Parse rewrite equiv arguments. *)
  let p_rw_equiv (rw_arg : Args.rw_equiv_item) (s : S.t) : rw_equiv =
    match rw_arg.rw_type with
    | `Rw f ->
      let dir = L.unloc rw_arg.rw_dir in

      let _, context, pat =
        S.convert_pt_gen ~check_compatibility:false f Equiv.Global_t s
      in

      if pat.pat_tyvars <> [] then
        soft_failure (Failure "free type variables remaining") ;

      if not (Sv.is_empty pat.pat_vars) then
        soft_failure (Failure "universally quantified variables remaining") ;

      if rw_arg.rw_mult <> `Once then
        hard_failure (Failure "multiplicity information not allowed for \
                               rewrite equiv") ;

      let f = pat.pat_term in

      context,f,dir

  (*------------------------------------------------------------------*)
  (** {3 Case tactic} *)

  (** Type for case and destruct tactics handlers *)
  type c_handler =
    | CHyp of Ident.t

  type c_res = c_handler * S.sequent

  (** Case analysis on a timestamp *)
  let timestamp_case (ts : Term.term) s : S.sequent list =
    let system =
      match SE.get_compatible_expr (S.system s) with
        | Some e -> e
        | None -> soft_failure (Failure "underspecified systems")
    in
    let table  = S.table s in

    let mk_case (action,symbol,indices) : Vars.var list * Term.term =
      let env = ref (S.vars s) in
      let indices, s = Term.refresh_vars (`InEnv env) indices in

      let name =
        SystemExpr.action_to_term table system
          (Action.subst_action s action)
      in
      (* FIXME: is this second substitution useful ? *)
      let name = Term.subst s name in

      indices, name
    in

    let cases = List.map mk_case (SystemExpr.actions table system) in

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
      S.Reduce.reduce param s k f
    in
      S.map { call = mapper } s

  (** Reduce the goal *)
  let reduce_goal param s =
    S.set_goal (S.Reduce.reduce param s S.conc_kind (S.goal s)) s

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
      n_ip ~dflt_name (ty : Type.ty) env : Vars.env * Vars.var =
    match n_ip with
    | Args.Unnamed
    | Args.AnyName     -> Vars.make `Approx env ty dflt_name
    | Args.Approx name -> Vars.make `Approx env ty name
    | Args.Named name  -> make_exact env ty name

  (*------------------------------------------------------------------*)
  (** Apply a naming pattern to a variable or hypothesis. *)
  let do_naming_pat
      (ip_handler : Args.ip_handler)
      (n_ip : Args.naming_pat)
      (s : S.t) : S.t
    =
    match ip_handler with
    | `Var v ->
      let env, v' =
        var_of_naming_pat n_ip ~dflt_name:(Vars.name v) (Vars.ty v) (S.vars s)
      in
      let subst = [Term.ESubst (Term.mk_var v, Term.mk_var v')] in

      (* FIXME: we substitute everywhere. This is inefficient. *)
      S.subst subst (S.set_vars env s)

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

      if S.Hyp.is_eq form then
        begin
          match S.Reduce.destr_eq s S.hyp_kind form with
          | Some (a,b) ->
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

          let vs_fresh, subst = Term.refresh_vars `Global vs in

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
      let pat = Term.pat_of_form f in
      let erule = pat_to_rw_rule s ~loc (S.system s).set (L.unloc dir) pat in
      let s, subgoals =
        rewrite ~loc ~all:false [T_conc] (`Once, Some id, erule) s
      in
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
        | x :: vs, f ->
          let x' = Vars.make_new_from x in

          let subst = [Term.ESubst (Term.mk_var x, Term.mk_var x')] in

          let f = S.Conc.mk_forall ~simpl:false vs f in

          let new_formula = S.subst_conc subst f in
          ( `Var x',
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

    else if S.Conc.is_neq form then
      begin
        let u, v = oget (S.Conc.destr_neq form) in
        let h = Term.mk_atom `Eq u v in
        let h = S.unwrap_hyp (`Reach h) in
        let id, s = Hyps.add_i Args.Unnamed h s in
        let s = S.set_goal S.Conc.mk_false s in
        `Hyp id, s
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
    let env = Vars.rm_vars (Sv.elements clear) (S.vars s) in
    S.set_vars env s

  let _generalize ~dependent t s : Vars.var * S.t =
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
            if Vars.Sv.mem v (S.fv_hyp f)
            then S.hyp_to_conc f :: gen_hyps, Hyps.remove id s
            else gen_hyps, s
          ) s ([], s)
    in

    let goal = S.Conc.mk_impls ~simpl:true gen_hyps (S.goal s) in
    v, S.set_goal goal s

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
      List.fold_left (fun vars t ->
          Sv.union vars (Term.fv t)
        ) Sv.empty terms
    in
    let s = try_clean_env t_fv s in

    (* we rename generalized variables *)
    let _, new_vars, subst =
      List.fold_left2 (fun (env, new_vars, subst) v n_ip ->
          let env, v' =
            var_of_naming_pat n_ip ~dflt_name:"x" (Vars.ty v) env
          in
          env,
          v' :: new_vars,
          Term.ESubst (Term.mk_var v, Term.mk_var v') :: subst
        ) (S.vars s, [], []) vars n_ips
    in
    let s = S.subst subst s in

    (* quantify universally *)
    let new_vars = List.rev new_vars in
    let goal = S.Conc.mk_forall ~simpl:false new_vars (S.goal s) in
    S.set_goal goal s

  let naming_pat_of_term t =
    match t with
    | Term.Var v -> Args.Approx (Vars.name v) (* use the same name *)
    | _ -> Args.AnyName

  let generalize_tac_args ~dependent args s : S.t list =
    match args with
    | [Args.Generalize (terms, n_ips_opt)] ->
      let terms =
        List.map (fun arg ->
            match convert_args s [Args.Theory arg] (Args.Sort Args.Term) with
            | Args.Arg (Args.Term (_, t, _)) -> t

            | _ -> bad_args ()
          ) terms
      in
      let n_ips =
        match n_ips_opt with
        | None -> List.map naming_pat_of_term terms
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

      In local and global sequents, we can apply an hypothesis
      to derive the goal or to derive the conclusion of an hypothesis.
      The former corresponds to [apply] below and the latter corresponds
      to [apply_in].

      TODO update [apply] and [apply_in] to make sure that they properly
        handle global and local hypotheses, and system annotations

      We impose in both that the hypotheses involved here are of the same
      kind as conclusion formulas: this is immediate for global sequents
      and, in the case of local sequents, means that we only consider
      local hypotheses. This might be generalized later, or complemented
      with other tactics that would have to generate global sequents
      as premisses. *)

  let apply ~use_fadup (pat : S.conc_form Term.pat) (s : S.t) : S.t list =
    let option =
      { Match.default_match_option with mode = `EntailRL; use_fadup }
    in
    let table, system, goal = S.table s, S.system s, S.goal s in

    let rec _apply (subs : S.conc_form list) (pat : S.conc_form Term.pat) =
      if not (Vars.Sv.subset pat.pat_vars (S.fv_conc pat.pat_term)) then
        soft_failure ApplyBadInst;

      let match_res =
        match S.conc_kind with
        | Local_t  -> Match.T.try_match ~option table system goal pat
        | Global_t -> Match.E.try_match ~option table system goal pat
        | Any_t -> assert false (* cannot happen *)
      in

      (* Check that [pat] entails [S.goal s]. *)
      match match_res with
      (* match failed by [pat] is a product: retry with the rhs *)
      | (NoMatch _ | FreeTyv) when S.Conc.is_impl pat.pat_term ->
        let t1, t2 = oget (S.Conc.destr_impl pat.pat_term) in
        _apply (t1 :: subs) { pat with pat_term = t2 }

      (* match failed, [pat] is not a product: user-level error *)
      | NoMatch minfos  -> soft_failure (ApplyMatchFailure minfos)
      | FreeTyv         -> soft_failure (ApplyMatchFailure None)

      (* match succeeded *)
      | Match mv ->
        let subst = Match.Mvar.to_subst ~mode:`Match mv in

        let goals = List.map (S.subst_conc subst) (List.rev subs) in
        List.map (fun g -> S.set_goal g s) goals
    in
    _apply [] pat

  (** [apply_in f hyp s] tries to match a premise of [f] with the conclusion of
      [hyp], and replaces [hyp] by the conclusion of [f].
      It generates a new subgoal for any remaining premises of [f], plus all
      premises of the original [hyp].

      E.g., if `H1 : A -> B` and `H2 : A` then `apply H1 in H2` replaces
      `H2 : A` by `H2 : B`. *)
  let apply_in
      ~use_fadup
      (pat : S.conc_form Term.pat)
      (hyp : Ident.t)
      (s : S.t) : S.t list
    =
    let fprems, fconcl = S.Conc.decompose_impls_last pat.pat_term in

    let h = Hyps.by_id hyp s in
    let h = S.hyp_to_conc h in
    let hprems, hconcl = S.Conc.decompose_impls_last h in

    let try1 (fprem : S.conc_form) =
      if not (Vars.Sv.subset pat.pat_vars (S.fv_conc fprem)) then None
      else
        let pat = { pat with pat_term = fprem } in
        let option =
          Match.{ default_match_option with mode = `EntailLR; use_fadup; }
        in

        let table = S.table s in
        let system = S.system s in
        let match_res =
          match S.conc_kind with
          | Local_t  -> Match.T.try_match ~option table system hconcl pat
          | Global_t -> Match.E.try_match ~option table system hconcl pat
          | Any_t -> assert false (* cannot happen *)
        in

        (* Check that [hconcl] entails [pat]. *)
        match match_res with
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


  (** for now, there is only one named optional arguments to `apply` *)
  let p_apply_fadup_arg (nargs : Args.named_args) : bool =
    match nargs with
    | [Args.NArg L.{ pl_desc = "inductive" }] -> true
    | (Args.NArg l) :: _ ->
      hard_failure ~loc:(L.loc l) (Failure "unknown argument")
    | [] -> false

  (** Parse apply tactic arguments. *)
  let p_apply_args
      (args : Args.parser_arg list)
      (s : S.sequent) : bool * S.conc_form Term.pat * target
    =
    let nargs, pat, in_opt =
      match args with
      | [Args.ApplyIn (nargs, pt,in_opt)] ->
        let _, pat = S.convert_pt ~close_pats:false pt S.conc_kind s in
        nargs, pat, in_opt

      | _ -> bad_args ()
    in

    let use_fadup = p_apply_fadup_arg nargs in

    let target = match in_opt with
      | Some lsymb -> T_hyp (fst (Hyps.by_name lsymb s))
      | None       -> T_conc
    in
    use_fadup, pat, target


  let apply_tac_args (args : Args.parser_arg list) s : S.t list =
    let use_fadup, pat, target = p_apply_args args s in
    match target with
    | T_conc    -> apply    ~use_fadup pat s
    | T_hyp id  -> apply_in ~use_fadup pat id s
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
    let v, vs = match vs0 with
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
            (v' :: vs)
            (S.Conc.mk_impl ~simpl:false
               (atom_lt)
               (S.subst_conc [Term.ESubst (Term.mk_var v,Term.mk_var v')] f))
        in

        let new_goal =
          S.Conc.mk_forall ~simpl:false
            [v]
            (S.Conc.mk_impl ~simpl:false
               ih
               (S.Conc.mk_forall ~simpl:false vs f))
        in

        [S.set_goal new_goal s]
      end
    | _ -> error ()

  let induction_gen ~dependent (t : Term.term) s : S.t list =
    let s = generalize ~dependent [t] [naming_pat_of_term t] s in
    induction s

  let induction_args ~dependent args s =
    match args with
    | [] -> induction s
    | [Args.Theory t] ->
      begin
        match convert_args s args (Args.Sort Args.Timestamp) with
        | Args.Arg (Args.Message (t, _)) -> induction_gen ~dependent t s
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

    let nu = Theory.parse_subst (S.env s) vs ths in
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

  (** [use ip name ths s] applies the formula named [name] in sequent [s],
    * eliminating its universally quantified variables using [ths],
    * eliminating implications (and negations) underneath.
    * If given an introduction pattern [ip], applies it to the generated
    * hypothesis.
    * As with apply, we require that the hypothesis (or lemma) is
    * of the kind of conclusion formulas: for local sequents this means
    * that we cannot use a global hypothesis or lemma. *)
  let use ~(mode:[`IntroImpl | `None]) ip (pt : Theory.p_pt) (s : S.t) =
    let _, pat = S.convert_pt pt S.conc_kind s in

    if pat.pat_tyvars <> [] then
      soft_failure (Failure "free type variables remaining") ;

   (* rename cleanly the variables *)
    let vars, subst =
      Term.refresh_vars (`InEnv (ref (S.vars s))) (Sv.elements pat.pat_vars)
    in
    let f = S.subst_conc subst pat.pat_term in
    let f =
      S.Conc.mk_forall ~simpl:true vars f
    in

    (* If [mode=`IntroImpl], compute subgoals by introducing implications
       on the left. *)
    let rec aux subgoals form =
      if S.Conc.is_impl form && mode = `IntroImpl then
        begin
          let h, c = oget (S.Conc.destr_impl form) in
          let s' = S.set_goal h s in
          aux (s'::subgoals) c
        end

      else if S.Conc.is_not form && mode = `IntroImpl then
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
            | Some ip -> do_simpl_pat (`Hyp idf) ip s0
          in

          match mode with
          | `None -> (List.rev subgoals) @ s0
          | `IntroImpl -> s0 @ List.rev subgoals (* legacy behavior *)
        end
    in

    aux [] f

  (*------------------------------------------------------------------*)
  (** {3 Assert} *)

  (** [tac_assert f j sk fk] generates two subgoals, one where [f] needs
    * to be proved, and the other where [f] is assumed.
    * We only consider the case here where [f] is a local formula
    * (which is then converted to conclusion and hypothesis formulae)
    * more general forms should be allowed here or elsewhere. *)
  let have_form (args : Args.parser_arg list) s : S.t list =
    let ip, f = match args with
      | [f] -> None, f
      | [f; Args.SimplPat ip] -> Some ip, f
      | _ -> bad_args () in

    let f = match convert_args s [f] Args.(Sort Boolean) with
      | Args.(Arg (Message (f,_))) -> f
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

  let have_args = function
    | [Args.AssertPt (pt, ip, mode)] -> use ~mode ip pt
    | _ as args -> have_form args

  let have_tac args = wrap_fail (have_args args)


  (*------------------------------------------------------------------*)
  (** {3 Depends} *)

  let depends Args.(Pair (Message (a1,_), Message (a2,_))) s =
    let models = S.get_models s in
    let get_action ts =
      match Constr.find_eq_action models ts with
      | Some ts -> ts
      | None ->
        soft_failure
          (Failure (Fmt.str "cannot find a action equal to %a" Term.pp ts))
    in

    match get_action a1, get_action a2 with
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
          (Tactics.NotDepends (Fmt.str "%a" Term.pp a1,
                               Fmt.str "%a" Term.pp a2))

    | _ -> assert false

  (*------------------------------------------------------------------*)
  (** {3 Namelength} *)


  let namelength
      Args.(Pair (Message (tn, tyn), Message (tm, tym)))
      (s : S.t) : S.t list
    =
    match tn, tm with
    | Name n, Name m ->
      let table = S.table s in

      (* FEATURE: subtypes *)
      if not (tyn = tym) then
        Tactics.soft_failure (Failure "names are not of the same types");

      if not Symbols.(check_bty_info table n.s_typ Ty_name_fixed_length) then
        Tactics.soft_failure
          (Failure "names are of a type that is not [name_fixed_length]");

      let f =
        Term.mk_atom `Eq
          (Term.mk_len (Term.mk_name n))
          (Term.mk_len (Term.mk_name m))
      in
      let f = Equiv.Babel.convert f ~src:Equiv.Local_t ~dst:S.conc_kind in

      [S.set_goal (S.Conc.mk_impl ~simpl:false f (S.goal s)) s]

    | _ -> Tactics.(soft_failure (Failure "expected names"))

  (*------------------------------------------------------------------*)
  (** {3 Remember} *)

  let remember (id : Theory.lsymb) (term : Theory.term) s =
    let t, ty = convert s term in
    let env, x = make_exact ~loc:(L.loc id) (S.vars s) ty (L.unloc id) in
    let subst = [Term.ESubst (t, Term.mk_var x)] in

    let s = S.subst subst (S.set_vars env s) in
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
  (** Split a conjunction conclusion, creating one subgoal per conjunct. *)
  let goal_and_right (s : S.t) : S.t list =
    match S.Conc.destr_and (S.goal s) with
    | Some (lformula, rformula) ->
      [ S.set_goal lformula s ;
        S.set_goal rformula s ]

    | None -> soft_failure (Failure "not a conjunction")

end

(*------------------------------------------------------------------*)
(** {2 Wrapper lifting sequence functions or tactics to general tactics} *)

module TS = TraceSequent
module ES = EquivSequent


(** Function over a [Goal.t], returning an arbitrary value. *)
type 'a genfun = Goal.t -> 'a

(** Function over an trace sequent, returning an arbitrary value. *)
type 'a tfun = TS.t -> 'a

(** Function over an equivalence sequent, returning an arbitrary value. *)
type 'a efun = ES.t -> 'a

(*------------------------------------------------------------------*)
(** Lift a [tfun] to a [genfun].
  * (user-level failure when the goal is not a trace sequent). *)
let genfun_of_tfun (t : 'a tfun) : 'a genfun = fun s ->
  match s with
  | Goal.Trace s -> t s
  | _ -> soft_failure (Tactics.Failure "local sequent expected")

(** As [genfun_of_tfun], but with an extra argument. *)
let genfun_of_tfun_arg
    (t : 'b -> TS.t -> 'a)
    (arg : 'b)
    (s : Goal.t) : 'a
  =
  match s with
  | Goal.Trace s -> t arg s
  | _ -> soft_failure (Tactics.Failure "local sequent expected")

(*------------------------------------------------------------------*)
(** Lift an [efun] to a [genfun].
  * (user-level failure when the goal is not an equivalence sequent). *)
let genfun_of_efun (t : 'a efun) : 'a genfun = fun s ->
  match s with
  | Goal.Equiv s -> t s
  | _ -> soft_failure (Tactics.Failure "global sequent expected")

(** As [genfun_of_efun], but with an extra argument. *)
let genfun_of_efun_arg
    (t : 'b -> ES.t -> 'a)
    (arg : 'b)
    (s : Goal.t) : 'a
  =
  match s with
  | Goal.Equiv s -> t arg s
  | _ -> soft_failure (Tactics.Failure "global sequent expected")

(*------------------------------------------------------------------*)
let genfun_of_any_fun (tt : 'a tfun) (et : 'a efun) : 'a genfun = fun s ->
  match s with
  | Goal.Trace s -> tt s
  | Goal.Equiv s -> et s

let genfun_of_any_fun_arg
    (tt : 'b -> 'a tfun)
    (et : 'b -> 'a efun)
    (arg : 'b)
    (s : Goal.t) : 'a
  =
  match s with
  | Goal.Trace s -> tt arg s
  | Goal.Equiv s -> et arg s

(*------------------------------------------------------------------*)
(** Function expecting and returning trace sequents. *)
type pure_tfun = TS.t -> TS.t list

let genfun_of_pure_tfun
    (t : pure_tfun)
    (s : Goal.t) : Goal.t list
  =
  let res = genfun_of_tfun t s in
  List.map (fun s -> Goal.Trace s) res

let genfun_of_pure_tfun_arg
    (t : 'a -> pure_tfun)
    (arg : 'a)
    (s : Goal.t) : Goal.t list
  =
  let res = genfun_of_tfun_arg t arg s in
  List.map (fun s -> Goal.Trace s) res

(*------------------------------------------------------------------*)
(** Function expecting and returning equivalence sequents. *)
type pure_efun = ES.t -> ES.t list

let genfun_of_pure_efun
    (t : pure_efun)
    (s : Goal.t) : Goal.t list
  =
  let res = genfun_of_efun t s in
  List.map (fun s -> Goal.Equiv s) res

let genfun_of_pure_efun_arg
    (t : 'a -> pure_efun)
    (arg : 'a)
    (s : Goal.t) : Goal.t list
  =
  let res = genfun_of_efun_arg t arg s in
  List.map (fun s -> Goal.Equiv s) res

(*------------------------------------------------------------------*)
let genfun_of_any_pure_fun
    (tt : pure_tfun)
    (et : pure_efun) : Goal.t list genfun
  =
  fun s ->
  match s with
  | Goal.Trace s -> List.map (fun s -> Goal.Trace s) (tt s)
  | Goal.Equiv s -> List.map (fun s -> Goal.Equiv s) (et s)

let genfun_of_any_pure_fun_arg
    (tt : 'a -> pure_tfun)
    (et : 'a -> pure_efun)
    (arg : 'a)
    (s : Goal.t) : Goal.t list
  =
  match s with
  | Goal.Trace s -> List.map (fun s -> Goal.Trace s) (tt arg s)
  | Goal.Equiv s -> List.map (fun s -> Goal.Equiv s) (et arg s)

(*------------------------------------------------------------------*)
(** General tactic *)
type gentac = Goal.t Tactics.tac

(** Tactic acting and returning trace goals *)
type ttac = TS.t Tactics.tac

(** Tactic acting and returning equivalence goals *)
type etac = ES.t Tactics.tac

(*------------------------------------------------------------------*)
(** Lift a [ttac] to a [gentac]. *)
let gentac_of_ttac (t : ttac) : gentac = fun s sk fk ->
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Goal.Trace s) l) fk) fk
  in
  genfun_of_tfun t' s sk fk

(** As [gentac_of_etac], but with an extra arguments. *)
let gentac_of_ttac_arg (t : 'a -> ttac) (a : 'a) : gentac = fun s sk fk ->
  let t' s sk fk =
    t a s (fun l fk -> sk (List.map (fun s -> Goal.Trace s) l) fk) fk
  in
  genfun_of_tfun t' s sk fk

(*------------------------------------------------------------------*)
(** Lift an [etac] to a [gentac]. *)
let gentac_of_etac (t : etac) : gentac = fun s sk fk ->
  let t' s sk fk =
    t s (fun l fk -> sk (List.map (fun s -> Goal.Equiv s) l) fk) fk
  in
  genfun_of_efun t' s sk fk

(** As [gentac_of_etac], but with an extra arguments. *)
let gentac_of_etac_arg (t : 'a -> etac) (a : 'a) : gentac = fun s sk fk ->
  let t' s sk fk =
    t a s (fun l fk -> sk (List.map (fun s -> Goal.Equiv s) l) fk) fk
  in
  genfun_of_efun t' s sk fk

(*------------------------------------------------------------------*)
let gentac_of_any_tac (tt : ttac) (et : etac) : gentac = fun s sk fk ->
  match s with
  | Goal.Trace s ->
    tt s (fun l fk -> sk (List.map (fun s -> Goal.Trace s) l) fk) fk

  | Goal.Equiv s ->
    et s (fun l fk -> sk (List.map (fun s -> Goal.Equiv s) l) fk) fk

let gentac_of_any_tac_arg
    (tt : 'a -> ttac)
    (et : 'a -> etac)
    (arg : 'a) : gentac
  =
  fun s sk fk ->
  match s with
  | Goal.Trace s ->
    tt arg s (fun l fk -> sk (List.map (fun s -> Goal.Trace s) l) fk) fk

  | Goal.Equiv s ->
    et arg s (fun l fk -> sk (List.map (fun s -> Goal.Equiv s) l) fk) fk

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

(** same as [CommonLT.wrap_fail], but for goals *)
let wrap_fail f s sk fk =
  try sk (f s) fk with
  | Tactics.Tactic_soft_failure e -> fk e

let split_equiv_goal (i : int L.located) (s : ES.t) =
  try List.splitat (L.unloc i) (ES.goal_as_equiv s)
  with List.Out_of_range ->
    soft_failure ~loc:(L.loc i) (Tactics.Failure "out of range position")

(*------------------------------------------------------------------*)
(** {2 Basic tactics} *)

module TraceLT = MkCommonLowTac (TS)
module EquivLT = MkCommonLowTac (ES)


(*------------------------------------------------------------------*)
(** {3 Rewrite} *)

type f_simpl =
  red_param:Reduction.red_param ->
  strong:bool -> close:bool ->
  Goal.t Tactics.tac

let do_s_item
    (simpl : f_simpl)
    (s_item : Args.s_item)
    (s : Goal.t) : Goal.t list
  =
  let s_item_body, args = s_item in
  let red_param = Reduction.rp_default in
  let red_param = Reduction.parse_simpl_args red_param args in
  match s_item_body with
  | Args.Simplify l ->
    let tac = simpl ~red_param ~strong:true ~close:false in
    Tactics.run tac s

  | Args.Tryauto l ->
    let tac = Tactics.try_tac (simpl ~red_param ~strong:true ~close:true) in
    Tactics.run tac s

  | Args.Tryautosimpl l ->
    let tac =
      Tactics.andthen         (* FIXME: inneficient *)
        (Tactics.try_tac (simpl ~red_param ~strong:true ~close:true))
        (simpl ~red_param ~strong:true ~close:false)
    in
    Tactics.run tac s

(* lifting to [Goal.t] *)
let do_rw_item
    (rw_item : Args.rw_item)
    (rw_in : Args.in_target) : Goal.t -> Goal.t list
  =
  Goal.map_list
    (TraceLT.do_rw_item rw_item rw_in)
    (EquivLT.do_rw_item rw_item rw_in)

(** Applies a rewrite arg  *)
let do_rw_arg
    (simpl : f_simpl)
    (rw_arg : Args.rw_arg)
    (rw_in : Args.in_target)
    (s : Goal.t) : Goal.t list
  =
  match rw_arg with
  | Args.R_item rw_item  -> do_rw_item rw_item rw_in s
  | Args.R_s_item s_item -> do_s_item simpl s_item s (* targets ignored *)

let rewrite_tac
    (simpl : f_simpl)
    (args : Args.parser_args)
    (s : Goal.t) : Goal.t list
  =
  match args with
  | [Args.RewriteIn (rw_args, in_opt)] ->
    List.fold_left (fun seqs rw_arg ->
        List.concat_map (do_rw_arg simpl rw_arg in_opt) seqs
      ) [s] rw_args

  | _ -> bad_args ()

let rewrite_tac (simpl : f_simpl) args : gentac =
  wrap_fail (rewrite_tac simpl args)

(*------------------------------------------------------------------*)
(** {3 Intro} *)

(* lifting to [Goal.t] *)
let do_intro_pat (ip : Args.simpl_pat) : Goal.t -> Goal.t list =
  Goal.map_list (TraceLT.do_intro_pat ip) (EquivLT.do_intro_pat ip)

(* lifting to [Goal.t] *)
let do_intro (s : Goal.t) : Args.ip_handler * Goal.t =
  match s with
  | Goal.Trace s ->
    let handler, s = TraceLT.do_intro s in
    handler, Goal.Trace s
  | Goal.Equiv s ->
    let handler, s = EquivLT.do_intro s in
    handler, Goal.Equiv s

(* lifting to [Goal.t] *)
let do_intro_var (s : Goal.t) : Args.ip_handler * Goal.t =
  match s with
  | Goal.Trace s ->
    let handler, s = TraceLT.do_intro_var s in
    handler, Goal.Trace s
  | Goal.Equiv s ->
    let handler, s = EquivLT.do_intro_var s in
    handler, Goal.Equiv s

(* lifting to [Goal.t] *)
let do_naming_pat
    (ip_handler : Args.ip_handler)
    (n_ip : Args.naming_pat) : Goal.t -> Goal.t
  =
  Goal.map
    (TraceLT.do_naming_pat ip_handler n_ip)
    (EquivLT.do_naming_pat ip_handler n_ip)

let rec do_intros_ip
    (simpl : f_simpl)
    (intros : Args.intro_pattern list)
    (s : Goal.t) : Goal.t list
  =
  match intros with
  | [] -> [s]

  | Args.SItem s_item :: intros ->
    do_intros_ip_list simpl intros (do_s_item simpl s_item s)

  | Args.Simpl s_ip :: intros ->
    let ss = do_intro_pat s_ip s in
    do_intros_ip_list simpl intros ss

  | Args.SExpnd s_e :: intros ->
    let ss = do_rw_item (s_e :> Args.rw_item) `Goal s in
    let ss = as_seq1 ss in (* we get exactly one new goal *)
    do_intros_ip simpl intros ss

  | Args.StarV loc :: intros0 ->
    let repeat, s =
      try
        let handler, s = do_intro_var s in
        true, do_naming_pat handler Args.AnyName s

      with Tactics.Tactic_soft_failure (_,NothingToIntroduce) ->
        false, s
    in
    let intros = if repeat then intros else intros0 in
    do_intros_ip simpl intros s

  | Args.Star loc :: intros ->
    try
      let handler, s = do_intro s in
      let s = do_naming_pat handler Args.AnyName s in
      do_intros_ip simpl (Args.Star loc :: intros) s

    with Tactics.Tactic_soft_failure (_,NothingToIntroduce) ->
      do_intros_ip simpl intros s

and do_intros_ip_list
    (simpl : f_simpl)
    (intros : Args.intro_pattern list)
    (ss : Goal.t list) : Goal.t list
  =
  List.concat_map (do_intros_ip simpl intros) ss


let intro_tac_args (simpl : f_simpl) args (s : Goal.t) : Goal.t list =
  match args with
  | [Args.IntroPat intros] -> do_intros_ip simpl intros s
  | _ -> bad_args ()

let intro_tac (simpl : f_simpl) args : gentac =
  wrap_fail (intro_tac_args simpl args)

(*------------------------------------------------------------------*)
(** Admit tactic *)

let () =
  T.register_general "admit"
    ~tactic_help:{
      general_help = "Admit the current goal, or admit an element \
                      from a  bi-frame.";
      detailed_help = "This tactic, of course, is not sound";
      usages_sorts = [Sort Args.Int];
      tactic_group = Logical}
    ~pq_sound:true
    (function
      | [] -> fun _ sk fk -> sk [] fk
      | [Args.Int_parsed i] ->
        begin
          fun s sk fk ->
            match s with
            | Goal.Trace _ -> bad_args ()
            | Goal.Equiv s ->
              let e = ES.change_felem ~loc:(L.loc i) (L.unloc i) [] s in
              sk [Goal.Equiv e] fk
        end
      | _ -> bad_args ())

(*------------------------------------------------------------------*)
(** {3 Fully factorized tactics} *)

(*------------------------------------------------------------------*)
let () =
  T.register_general "clear"
    ~tactic_help:{
      general_help = "Clear an hypothesis.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.clear_tac EquivLT.clear_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "revert"
    ~tactic_help:{
      general_help = "Take an hypothesis H, and turns the conclusion C into \
                      the implication H => C.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.revert_tac EquivLT.revert_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "remember"
    ~tactic_help:{
      general_help = "substitute a term by a fresh variable";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (gentac_of_any_tac_arg TraceLT.remember_tac EquivLT.remember_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "generalize"
    ~tactic_help:{
      general_help = "Generalize the goal on some terms";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (gentac_of_any_tac_arg
       (TraceLT.generalize_tac ~dependent:false)
       (EquivLT.generalize_tac ~dependent:false))

let () =
  T.register_general "generalize dependent"
    ~tactic_help:{
      general_help = "Generalize the goal and hypotheses on some terms";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts = []; }
    (gentac_of_any_tac_arg
       (TraceLT.generalize_tac ~dependent:true)
       (EquivLT.generalize_tac ~dependent:true))

(*------------------------------------------------------------------*)
let () = T.register_general "reduce"
    ~tactic_help:{general_help = "Reduce the sequent.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.reduce_tac EquivLT.reduce_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "destruct"
    ~tactic_help:{
      general_help = "Destruct an hypothesis. An optional And/Or \
                      introduction pattern can be given.\n\n\
                      Usages: destruct H.\n\
                     \        destruct H as [A | [B C]]";
      detailed_help = "";
      usages_sorts = [];
      tactic_group = Logical}
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.destruct_tac EquivLT.destruct_tac)

(*------------------------------------------------------------------*)
let () =
  T.register_general "exists"
    ~tactic_help:{
      general_help = "Introduce the existentially quantified \
                      variables in the conclusion of the judgment, \
                      using the arguments as existential witnesses.\
                      \n\nUsage: exists v1, v2, ...";
      detailed_help = "";
      usages_sorts = [];
      tactic_group = Logical}
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.exists_intro_tac EquivLT.exists_intro_tac)


(*------------------------------------------------------------------*)
let () =
  T.register_general "have"
    ~tactic_help:
      {general_help = "Add a new hypothesis.";
       detailed_help =
         "- have form:\n\
         \  Add `form` to the hypotheses, and produce a subgoal to prove \
          `form`. \n\
          - have form as intro_pat:\n\
         \  Idem, except that `intro_pat` is applied to `form`.\n\
          - have intro_pat := proof_term:\n\
         \  Compute the formula corresponding to `proof_term`, and\n\
         \  apply `intro_pat` to it.\n\
         \  Exemples: * `have H := H0 i i2`\n\
         \            * `have H := H0 _ i2`";
       usages_sorts = [];
       tactic_group = Logical}
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.have_tac EquivLT.have_tac)

(*------------------------------------------------------------------*)
(* The `use` tacitcs now rely on the same code as the `assert` tactic.
   We still register a tactic to have the tactic help working correctly. *)
let () =
  T.register_general "use"
    ~tactic_help:
      {general_help = "Instantiate a lemma or hypothesis on some arguments.\n\n\
                       Usages: use H with v1, ..., vn\n\
                      \        use H with v1 as intro_pat";
       detailed_help = "";
       usages_sorts = [];
       tactic_group = Logical}
    ~pq_sound:true
    (fun _ _ _ -> assert false)


(*------------------------------------------------------------------*)
let () =
  T.register_general "apply"
    ~tactic_help:{
      general_help=
        "Matches the goal with the conclusion of the formula F provided \
         (directly, using lemma, or using an axiom), trying to instantiate \
         F variables. Creates one subgoal for each premises of F.\n\
         Usage: apply my_lem.\n
         apply my_axiom.";
      detailed_help="";
      usages_sorts=[];
      tactic_group=Structural}
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.apply_tac EquivLT.apply_tac)

(*------------------------------------------------------------------*)
let () = T.register_general "dependent induction"
    ~tactic_help:{general_help = "Apply the induction scheme to the conclusion.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (gentac_of_any_tac_arg
       (TraceLT.induction_tac ~dependent:true)
       (EquivLT.induction_tac ~dependent:true))

(*------------------------------------------------------------------*)
(* we are only registering the help here *)
let () =
  T.register "print"
    ~tactic_help:{general_help = "Shows the current system.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (genfun_of_any_pure_fun (fun _ -> assert false) (fun _ -> assert false))

(*------------------------------------------------------------------*)
let () = T.register_general "show"
    ~tactic_help:{
      general_help  = "Print the messages given as argument. Can be used to \
                       print the values matching a pattern.";
      detailed_help = "";
      tactic_group  = Logical;
      usages_sorts  = [Sort Args.Message]; }
    (gentac_of_any_tac_arg TraceLT.print_messages_tac EquivLT.print_messages_tac)


(*------------------------------------------------------------------*)
let () =
  T.register_typed "depends"
    ~general_help:"If the second action depends on the first \
                   action, and if the second \
                   action happened, \
                   add the corresponding timestamp inequality."
    ~detailed_help:"Whenever action A1[i] must happen before A2[i], if A2[i] \
                    occurs in the trace, we can add A1[i]. "
    ~tactic_group:Structural
    ~pq_sound:true
    (genfun_of_any_pure_fun_arg TraceLT.depends EquivLT.depends)
    Args.(Pair (Timestamp, Timestamp))


(*------------------------------------------------------------------*)
let () =
  T.register_typed "namelength"
    ~general_help:"Adds the fact that two names have the same length."
    ~detailed_help:""
    ~tactic_group:Structural
    ~pq_sound:true
    (genfun_of_any_pure_fun_arg TraceLT.namelength EquivLT.namelength)
    Args.(Pair (Message, Message))

(*------------------------------------------------------------------*)
let () = T.register_general "expand"
    ~tactic_help:{
      general_help  = "Expand all occurences of the given macro inside the \
                       goal.";
      detailed_help = "Can only be called over macros with fully defined \
                       timestamps.";
      tactic_group  = Structural;
      usages_sorts  = [Sort Args.String; Sort Args.Message; Sort Args.Boolean]; }
    ~pq_sound:true
    (gentac_of_any_tac_arg TraceLT.expand_tac EquivLT.expand_tac)

(*------------------------------------------------------------------*)
let () = T.register "expandall"
    ~tactic_help:{
      general_help  = "Expand all possible macros in the sequent.";
      detailed_help = "";
      tactic_group  = Structural;
      usages_sorts  = []; }
    ~pq_sound:true
    (genfun_of_any_pure_fun
       (TraceLT.expand_all_l `All)
       (EquivLT.expand_all_l `All))
(* FIXME: allow user to specify targets *)

(*------------------------------------------------------------------*)
let () = T.register "split"
    ~tactic_help:{general_help = "Split a conjunction conclusion, creating one \
                                  subgoal per conjunct.";
                  detailed_help = "G=> A & B is replaced by G=>A and goal G=>B.";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    ~pq_sound:true
    (genfun_of_any_pure_fun
       TraceLT.goal_and_right
       EquivLT.goal_and_right)
