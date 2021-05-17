open Utils

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
(** {2 Module type for sequents}*)

module type Sequent = sig
  type t
  type sequent = t

  val pp : Format.formatter -> t -> unit

  (** type of hypotheses and goals *)
  type hyp 

  module Hyps : Hyps.HypsSeq with type hyp = hyp and type sequent = t

  val reach_to_hyp : Term.message -> hyp

  val env : t -> Vars.env
  val set_env : Vars.env -> t -> t

  val goal : t -> hyp
  val set_goal : hyp -> t -> t
  val set_reach_goal : Term.message -> t -> t

  val system : t -> SystemExpr.system_expr
  val set_system : SystemExpr.system_expr -> t -> t

  val table : t -> Symbols.table
  val set_table  : Symbols.table -> t -> t

  val ty_vars : t -> Type.tvars 

  val is_hyp_or_lemma        : lsymb -> t -> bool
  val is_equiv_hyp_or_lemma  : lsymb -> t -> bool
  val is_reach_hyp_or_lemma  : lsymb -> t -> bool

  val get_hyp_or_lemma       : lsymb -> t -> Goal.hyp_or_lemma
  val get_equiv_hyp_or_lemma : lsymb -> t -> Goal.equiv_hyp_or_lemma
  val get_reach_hyp_or_lemma : lsymb -> t -> Goal.reach_hyp_or_lemma

  val query_happens : precise:bool -> t -> Term.timestamp -> bool

  val mk_trace_cntxt : t -> Constr.trace_cntxt

  val get_models : t -> Constr.models

  val subst     : Term.subst ->   t ->   t
  val subst_hyp : Term.subst -> hyp -> hyp

  (** get (some) terms appearing in an hypothesis.
      In an equiv formula, does not return terms under (equiv) binders. *)
  val get_terms : hyp -> Term.message list

  (** Matching in hypotheses *)
  module Match : Term.MatchS with type t = hyp
end

(*------------------------------------------------------------------*)
(** {2 Functor building tactics from a Sequent module}*)

module LowTac (S : Sequent) = struct

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
  let check_ty_eq ty1 ty2 = 
    if not (Type.equal ty1 ty2) then
      soft_failure 
        (Failure (Fmt.strf "types %a and %a are not compatible" 
                    Type.pp ty1 Type.pp ty2));
    ()

  (*------------------------------------------------------------------*)
  let check_hty_eq hty1 hty2 = 
    if not (Type.ht_equal hty1 hty2) then
      soft_failure 
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
  (** {3 Targets} *)
  type target = [`Goal | `Hyp of Ident.t]

  type targets = target list

  let target_all s : target list =
    `Goal :: List.map (fun ldecl -> `Hyp (fst ldecl)) (Hyps.to_list s)

  let make_in_targets (in_t : Args.in_target) (s : S.sequent) : targets * bool =
    match in_t with
    | `Hyps symbs -> 
      List.map (fun symb -> `Hyp (fst (Hyps.by_name symb s))) symbs, false
    | `All -> target_all s, true
    | `Goal -> [`Goal], false


  (* rewrite in a single target *)
  let do_target 
      (doit : (S.hyp * Ident.t option) -> S.hyp * S.hyp list) 
      (s : S.sequent) (t : target) : S.sequent * S.sequent list =
    let f, s, tgt_id = match t with
      | `Goal -> S.goal s, s, None
      | `Hyp id -> Hyps.by_id id s, Hyps.remove id s, Some id
    in

    let f,subs = doit (f,tgt_id) in
    let subs : S.sequent list = 
      List.map (fun sub -> S.set_goal sub s) subs
    in

    match t with
    | `Goal -> S.set_goal f s, subs
    | `Hyp id -> Hyps.add (Args.Named (Ident.name id)) f s, subs

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

    let doit (f,_) = S.subst_hyp subst f, [] in
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
        let form = match target with
          | `Goal   -> S.goal s
          | `Hyp id -> Hyps.by_id id s
        in
        find_occs_macro_terms ~st:occs m (S.get_terms form)
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

      let doit (f,_) = S.subst_hyp subst f, [] in
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

  (** A rewrite rule is a tuple: 
      (type variables, term variables, premisses, left term, right term)
      Invariant: if (tyvars,sv,φ,l,r) is a rewrite rule, then
      - sv ⊆ FV(l)
      - ((FV(r) ∪ FV(φ)) ∩ sv) ⊆ FV(l) *)
  type 'a rw_rule = 
    Type.tvars * Vars.Sv.t * Term.message list * 'a Term.term * 'a Term.term

  type rw_erule = Type.tvars * Vars.Sv.t * Term.message list * Term.esubst

  type rw_arg = 
    | Rw_rw of Ident.t option * rw_erule
    (* The ident is the ident of the hyp the rule came from (if any) *)

    | Rw_expand of Theory.term

  type rw_earg = Args.rw_count * rw_arg

  (** Check that the rule is correct. *)
  let check_erule ((_, sv, h, Term.ESubst (l,r)) : rw_erule) : unit =
    let fvl, fvr = Term.fv l, Term.fv r in
    let sh = List.fold_left (fun sh h ->
        Vars.Sv.union sh (Term.fv h)
      ) Vars.Sv.empty h
    in

    if not (Vars.Sv.subset sv fvl) || 
       not (Vars.Sv.subset (Vars.Sv.inter (Vars.Sv.union fvr sh) sv) fvl) then 
      hard_failure Tactics.BadRewriteRule;
    ()


  (** [rewrite ~all tgt rw_args] rewrites [rw_arg] in [tgt].
      If [all] is true, then does not fail if no rewriting occurs. *)
  let rewrite ~all 
      (targets: target list) 
      (rw : Args.rw_count * Ident.t option * rw_erule) (s : S.sequent)
    : S.sequent * S.sequent list =
    let found1, cpt_occ = ref false, ref 0 in
    let built_subs = ref [] in

    (* Return: (f, subs) *)
    let rec doit
      : type a. Args.rw_count -> a rw_rule -> S.hyp -> S.hyp = 
      fun mult (tyvars, sv, rsubs, l, r) f ->

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
          let r1 = Term.cast (Term.kind occ) (Term.subst subst r) in
          let rsubs1 = 
            List.map (fun rsub ->
                Term.mk_forall ~simpl:true vars (Term.subst subst rsub)
              ) rsubs in
          built_subs := List.rev_append rsubs1 !built_subs;
          r1
        in

        (* tries to find an occurence of [l] and rewrite it. *)
        let pat = 
          Term.{ pat_tyvars = tyvars; pat_vars = sv; pat_term = l; } 
        in
        let many = match mult with `Once -> false | `Any | `Many -> true in

        let f_opt = S.Match.find_map ~many (S.env s) f pat rw_inst in

        match mult, f_opt with
        | `Any, None -> f

        | (`Once | `Many), None -> 
          if not all 
          then soft_failure Tactics.NothingToRewrite 
          else f

        | (`Many | `Any), Some f -> doit `Any (tyvars, sv, rsubs, l, r) f
        | `Once, Some f -> f
    in

    let is_same (hyp_id : Ident.t option) (target_id : Ident.t option) = 
      match hyp_id, target_id with
      | None, _ | _, None -> false
      | Some hyp_id, Some target_id ->
        Ident.name hyp_id = Ident.name target_id && 
        Ident.name hyp_id <> "_" 
    in

    let doit_tgt (f,tgt_id : S.hyp * Ident.t option) : S.hyp * S.hyp list =
      match rw with
      | mult,  id_opt, (tyvars, sv, subs, Term.ESubst (l,r)) ->
        if is_same id_opt tgt_id 
        then f, []
        else
          let f = doit mult (tyvars, sv, subs, l, r) f in
          let subs = List.rev !built_subs in
          f, List.map S.reach_to_hyp subs
    in

    let s, subs = do_targets doit_tgt s targets in

    if all && not !found1 then soft_failure Tactics.NothingToRewrite;

    s, subs

  (** Make a rewrite rule from a formula *)
  let form_to_rw_erule ?(ty_vars=[]) ?loc dir f : rw_erule = 
    let vs, f = Term.decompose_forall f in
    let vs, subst = Term.erefresh_vars `Global vs in
    let f = Term.subst subst f in

    let vs = Vars.Sv.of_list vs in

    let subs, f = Term.decompose_impls_last f in

    let e = match f with
      | Term.Atom (`Message   (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
      | Term.Atom (`Timestamp (`Eq, t1, t2)) -> Term.ESubst (t1,t2)
      | Term.Atom (`Index     (`Eq, t1, t2)) -> 
        Term.ESubst (Term.Var t1,Term.Var t2)
      | _ -> hard_failure ?loc (Tactics.Failure "not an equality") 
    in

    let e = match dir with
      | `LeftToRight -> e
      | `RightToLeft -> 
        let Term.ESubst (t1,t2) = e in
        Term.ESubst (t2,t1)
    in

    let rule = ty_vars, vs, subs, e in

    (* We check that the rule is valid *)
    check_erule rule;

    rule

  (** Parse rewrite tactic arguments as rewrite rules with possible subgoals 
      showing the rule validity. *)
  let p_rw_item (rw_arg : Args.rw_item) s : rw_earg * S.sequent list =
    let p_rw_rule dir (rw_type : Theory.formula) 
      : rw_erule * S.sequent list * Ident.t option = 
      match Args.convert_as_lsymb [Args.Theory rw_type] with
      | Some str when S.is_hyp_or_lemma str s ->
        let lem = S.get_reach_hyp_or_lemma str s in        
        let ty_vars = lem.gc_tyvars in
        let id_opt = match lem.gc_name with `Hyp id -> Some id | _ -> None in
        let f = lem.gc_concl in

        (* We are using an hypothesis, hence no new sub-goals *)
        let premise = [] in

        form_to_rw_erule ~ty_vars dir f, premise, id_opt

      | _ -> 
        let cenv = Theory.{ table = S.table s;
                            cntxt = InGoal; } in 
        let f = 
          Theory.convert cenv (S.ty_vars s) (S.env s) rw_type Type.Boolean 
        in

        (* create new sub-goal *)
        let premise = [S.set_reach_goal f s] in

        form_to_rw_erule ~loc:(L.loc rw_type) dir f, premise, None
    in

    let p_rw_item (rw_arg : Args.rw_item) : rw_earg * (S.sequent list) = 
      let rw, subgoals = match rw_arg.rw_type with
        | `Form f -> 
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

end
