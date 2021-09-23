(** All equivalence tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Strucutral -> relies on properties of protocols, or of equality over 
      messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be 
      assumed.
*)
 
open Utils

module T    = Prover.ProverTactics
module Args = TacticsArgs
module L    = Location
module SE   = SystemExpr

module ES   = EquivSequent
module Hyps = ES.Hyps
 
type sequent = ES.sequent

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

let split_equiv_goal = LowTactics.split_equiv_goal
                         
(*------------------------------------------------------------------*)
let wrap_fail = EquivLT.wrap_fail

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Build the sequent showing that a timestamp happens. *)
let happens_premise (s : ES.t) (a : Term.timestamp) =
  let s = ES.(to_trace_sequent (set_reach_goal (Term.mk_happens a) s)) in
  Goal.Trace s


(*------------------------------------------------------------------*)
exception NoReflMacros

let check_no_macro_or_var t =
  let exception Failed in

  let rec check (Term.ETerm t) =
    match t with
    | Term.Var _ | Term.Macro _ -> raise Failed
    | _ -> Term.titer check t
  in
  try check (Term.ETerm t); true with Failed -> false

(** Closes the goal if it is an equivalence
  * where the two frames are identical. *)
let refl (e : Equiv.equiv) (s : ES.t) =
  if not (List.for_all check_no_macro_or_var e)
  then `NoReflMacroVar
  else if ES.get_frame PLeft s = ES.get_frame PRight s
  then `True
  else `NoRefl


(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl_tac (s : ES.t) =
  match refl (ES.goal_as_equiv s) s with
    | `True           -> []
    | `NoRefl         -> soft_failure (Tactics.NoRefl)
    | `NoReflMacroVar -> soft_failure (Tactics.NoReflMacroVar)

let () =
  T.register "refl"
    ~tactic_help:{general_help = "Closes a reflexive goal.";
                  detailed_help = "A goal is reflexive when the left and right \
                                   frame corresponding to the bi-terms are \
                                   identical. This of course needs to be the \
                                   case also for macros expansions.";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (LowTactics.genfun_of_efun refl_tac)

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : sequent list =
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s ->
    let id, _ = Hyps.by_name str s in
    List.map
      (fun (EquivLT.CHyp _, ss) -> ss)
      (EquivLT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match EquivLT.convert_args s args Args.(Sort ETerm) with
    | Args.Arg (ETerm (ty, f, _)) ->
      begin
        match Type.kind ty with
        | Type.KTimestamp -> EquivLT.timestamp_case f s

        | Type.KMessage -> bad_args ()
        | Type.KIndex -> bad_args ()
      end
    | _ -> bad_args ()


let case_tac args = wrap_fail (do_case_tac args)

(*------------------------------------------------------------------*)
(** For each element of the biframe, checks that it is a member of the
  * hypothesis biframe. If so, close the goal. *)
let assumption s =
  let goal = ES.goal s in

  let in_atom =
    (* For equivalence goals, we look for inclusion of the goal in
       an existing equivalence hypothesis *)
    if ES.goal_is_equiv s then
      let goal = ES.goal_as_equiv s in
      (function
        | Equiv.Equiv equiv  ->
          List.for_all (fun elem -> List.mem elem equiv) goal
        | Equiv.Reach _ -> false)

    else (fun at -> Equiv.Atom at = goal)
  in

  let in_hyp _ = function
    | Equiv.Atom at -> in_atom at
    | _ as f -> f = goal
  in

  if Hyps.exists in_hyp s
  then []
  else Tactics.soft_failure Tactics.NotHypothesis

(*------------------------------------------------------------------*)
let byequiv s = Goal.Trace (ES.to_trace_sequent s)

let byequiv_tac s = [byequiv s]

let () =
  T.register "byequiv"
    ~tactic_help:{general_help = "transform an equivalence goal into a \
                                  reachability goal.";
                  detailed_help = "";
                  usages_sorts = [Sort None];
                  tactic_group = Logical}
    (LowTactics.genfun_of_efun byequiv_tac)


(*------------------------------------------------------------------*)
(** [tautology f s] tries to prove that [f] is always true in [s]. *)
let rec tautology f s = match f with
  | Equiv.Impl (f0,f1) ->
    let s = Hyps.add Args.AnyName f0 s in
    tautology f1 s

  | Equiv.And (f0,f1) ->
    tautology f0 s && tautology f1 s

  | Equiv.Or (f0,f1) ->
    tautology f0 s || tautology f1 s

  | Equiv.Quant _ -> false
  | Equiv.(Atom (Equiv e)) -> refl e s = `True
  | Equiv.(Atom (Reach _)) ->
    let s = ES.set_goal f s in
    let trace_s = ES.to_trace_sequent s in
    (* TODO: improve automation by doing more than just constraint solving ? *)
    TraceTactics.constraints trace_s

(** [form_simpl_impl f s] simplifies the formula [f] in [s], by trying to
    prove [f]'s hypotheses in [s]. *)
let rec form_simpl_impl f s = match f with
  | Equiv.Impl (f0, f1) ->
    if tautology f0 s then form_simpl_impl f1 s else f
  | _ -> f

let simpl_impl s =
  Hyps.mapi (fun id f ->
      let s_minus = Hyps.remove id s in
      form_simpl_impl f s_minus
    ) s


(*------------------------------------------------------------------*)
(* Simplification function doing nothing. *)
let simpl_ident : LowTactics.f_simpl = fun ~strong ~close s sk fk ->
  if close then fk (None, GoalNotClosed) else sk [s] fk

(*------------------------------------------------------------------*)
(** [generalize ts s] reverts all hypotheses that talk about [ts] in [s],
    by introducing them in the goal.
    Also returns a function that introduces back the generalized hypothesis.*)
let generalize (ts : Term.timestamp) s =
  let ts = match ts with
    | Var t -> Vars.EVar t
    | _ -> hard_failure (Failure "timestamp is not a var") in

  let gen_hyps = Hyps.fold (fun id f gen_hyps ->
      if Sv.mem ts (Equiv.fv f)
      then id :: gen_hyps
      else gen_hyps
    ) s [] in

  (* Generalized sequent *)
  let s = List.fold_left (fun s id -> EquivLT.revert id s) s gen_hyps in

  (* Function introducing back generalized hypotheses *)
  let intro_back (s : ES.t) : ES.t =
    let ips = List.rev_map (fun id ->
        let ip = Args.Named (Ident.name id) in
        Args.(Simpl (SNamed ip))
      ) gen_hyps
    in
    match LowTactics.do_intros_ip simpl_ident ips (Goal.Equiv s) with
    | [Goal.Equiv s] -> s
    | _ -> assert false
  in

  intro_back, s


(*------------------------------------------------------------------*)
(** Given a judgement [s] of the form Γ ⊢ E, and a timestamp τ,
    produce the judgments
    Γ ⊢ E{ts → init}   and   (Γ, E{ts → pred τ}) ⊢ E.
    The second one is then direclty simplified by a case on all possible
    values of τ, producing a judgement for each one.
    Generalizes Γ ⊢ E over τ if necessary. *)
let induction Args.(Timestamp ts) s =
  let env = ES.env s in
  match ts with
  | Var t as ts ->
    (* Generalizes over [ts]. *)
    let intro_back, s = generalize ts s in

    (* Remove ts from the sequent, as it will become unused. *)
    let s = ES.set_env (Vars.rm_var env t) s in
    let table  = ES.table s in
    let system = ES.system s in
    let subst = [Term.ESubst (ts, Term.mk_pred ts)] in
    let goal = ES.goal s in

    let ind_hyp = Equiv.subst subst goal in
    (* Introduce back generalized hypotheses. *)
    let induc_s = intro_back s in
    (* Introduce induction hypothesis. *)
    let id_ind, induc_s = Hyps.add_i (Args.Named "IH") ind_hyp induc_s in

    let init_goal = Equiv.subst [Term.ESubst(ts,Term.init)] goal in
    let init_s = ES.set_goal init_goal s in
    let init_s = intro_back init_s in

    let goals = ref [] in
    (** [add_action _action descr] adds to goals the goal corresponding to the
      * case where [t] is instantiated by [descr]. *)
    let add_action descr =
      if descr.Action.name = Symbols.init_action
      then ()
      else
        begin
          let env = ref @@ ES.env induc_s in
          let subst =
            List.map
              (fun i ->
                 let i' = Vars.fresh_r env i in
                 Term.ESubst (Term.mk_var i, Term.mk_var i'))
              descr.Action.indices
          in
          let name =
            SystemExpr.action_to_term table system
              (Action.subst_action subst descr.Action.action)
          in
          let ts_subst = [Term.ESubst(ts,name)] in
          goals := (ES.subst ts_subst induc_s
                    |> ES.set_env !env)
                   ::!goals
        end
    in

    SystemExpr.iter_descrs table system add_action ;

    List.map simpl_impl (init_s :: List.rev !goals)

  | _  ->
    soft_failure
      (Tactics.Failure "expected a timestamp variable")

(*------------------------------------------------------------------*)
(** Induction *)

let old_or_new_induction args =
  if Config.new_ind () then
    (EquivLT.induction_tac ~dependent:false) args
  else
    (fun s sk fk ->
       match EquivLT.convert_args s args (Args.Sort Args.Timestamp) with
       | Args.Arg (Args.Timestamp ts) ->
         let ss = induction (Args.Timestamp ts) s in
         sk ss fk
       | _ -> hard_failure (Failure "ill-formed arguments")
    )

(*------------------------------------------------------------------*)
let enrich (arg : Theory.eterm Args.arg) (s : ES.t) =
  match arg with
  | Args.ETerm (ty, f, loc) ->
    let elem : Term.message =
      match Type.equalk_w (Term.kind f) Type.KMessage with
      | Some Type.Type_eq -> f
      | None -> hard_failure (Tactics.Failure "expected a message")
    in
    ES.set_equiv_goal (elem :: ES.goal_as_equiv s) s

let enrich_a arg s =
  let tbl, env = ES.table s, ES.env s in
  match Args.convert_args tbl (ES.ty_vars s) env [arg] Args.(Sort ETerm) with
  | Args.Arg (ETerm _ as arg) -> enrich arg s
  | _ -> bad_args ()

let enrichs args s =
  List.fold_left (fun s arg -> enrich_a arg s) s args

let enrich_tac args s sk fk = 
  try sk [enrichs args s] fk with
  | Tactics.Tactic_soft_failure e -> fk e

let () =
  T.register_general "enrich"
    ~tactic_help:{
      general_help  = "Enrich the goal with the given term.";
      detailed_help = "This is usually called before the induction, to enrich the \
                       induction hypothesis, and then allow to solve multiple cases \
                       more simply.";
      tactic_group  = Logical;
      usages_sorts  = [Sort Args.Message; Sort Args.Boolean]; }
    (LowTactics.gentac_of_etac_arg enrich_tac)


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

(*------------------------------------------------------------------*)
(** Function application *)

exception No_common_head
exception No_FA

let fa_expand t =
  let aux : type a. a Term.term -> Equiv.equiv = function
    (* FIXME: this should be subsumed by reduce *)
    | Fun (f,_,[c;t;e]) when f = Term.f_ite && t = e ->
      ES.[ t ]

    | Fun (f,_,l) -> l

    | Atom (`Message (_,f,g)) ->
      ES.[ f ; g ]

    | Diff _ -> raise No_common_head
    | _ -> raise No_FA
  in

  (* FIXME: this may no longer be necessary (type changes) *)
  (* Remve of_bool(b) coming from expansion of frame macro *)
  let filterBoolAsMsg =
    List.map
      (fun x -> match x with
         | Term.Fun (f,_,[c])
           when f = Term.f_of_bool -> c
         | _ -> x)
  in
  filterBoolAsMsg (aux (Term.head_normal_biterm t))

let fa i s =
  let before, e, after = split_equiv_goal i s in
  try
    (* Special case for try find, otherwise we use fa_expand *)
    match e with
    | Find (vars,c,t,e) ->
      let env = ref (ES.env s) in
      let vars' = List.map (Vars.fresh_r env) vars in
      let subst =
        List.map2
          (fun i i' -> Term.ESubst (Term.mk_var i, Term.mk_var i'))
          vars vars'
      in
      let c' = Term.mk_seq0 (List.map Vars.evar vars) c in
      let t' = Term.subst subst t in
      let biframe =
        List.rev_append before
          (Equiv.[ c' ; t' ; e ] @ after)
      in
      [ ES.set_env !env (ES.set_equiv_goal biframe s) ]

    | Seq(vars,t) -> 
      let terms = fa_expand t in
      let biframe = 
        List.rev_append 
          before 
          ((List.map (fun t' -> Term.mk_seq0 ~simpl:true vars t') terms) @ after)
      in
      [ ES.set_equiv_goal biframe s ]

    | _ ->
      let biframe =
        List.rev_append before (fa_expand e @ after) in
      [ ES.set_equiv_goal biframe s ]
  with
  | No_common_head ->
    soft_failure (Tactics.Failure "No common construct")
  | No_FA ->
    soft_failure (Tactics.Failure "FA not applicable")

let fa_tac args = match args with
  | [Args.Int_parsed i] -> wrap_fail (fa i)
  | _ -> bad_args ()


(*------------------------------------------------------------------*)
(** This function goes over all elements inside elems.  All elements that can be
   seen as duplicates, or context of duplicates, are removed. All elements that
   can be seen as context of duplicates and assumptions are removed, but
   replaced by the assumptions that appear as there subterms. *)
let rec filter_fa_dup table res assump (elems : Equiv.equiv) =
  let rec is_fa_dup acc elems e =
    (* if an element is a duplicate wrt. elems, we remove it directly *)
    if Action.is_dup table e elems then
      (true,[])
    (* if an element is an assumption, we succeed, but do not remove it *)
    else if List.mem e assump then
      (true,[e])
    (* otherwise, we go recursively inside the sub-terms produced by function
       application *)
    else try
      let new_els = fa_expand e in
      List.fold_left
        (fun (aux1,aux2) e ->
          let (fa_succ,fa_rem) = is_fa_dup acc elems e in
          fa_succ && aux1, fa_rem @ aux2)
        (true,[]) new_els
    with No_FA | No_common_head -> (false,[])
  in
  match elems with
  | [] -> res
  | e :: els ->
    let (fa_succ,fa_rem) =  is_fa_dup [] (res@els) e in
    if fa_succ then filter_fa_dup table (fa_rem@res) assump els
    else filter_fa_dup table (e::res) assump els

(** This tactic filters the biframe through filter_fa_dup, passing the set of
   hypotheses to it.  This is applied automatically, and essentially leaves only
   assumptions, or elements that contain a subterm which is neither a duplicate
   nor an assumption. *)
let fa_dup s =
  let table = ES.table s in

  (* TODO: allow to choose the hypothesis through its id *)
  let hyp = Hyps.find_map (fun _id hyp -> match hyp with
      | Equiv.(Atom (Equiv e)) -> Some e
      | _ -> None) s in

  let hyp = Utils.odflt [] hyp in

  let biframe = ES.goal_as_equiv s
                |> List.rev
                |> filter_fa_dup table [] hyp
  in
  [ES.set_equiv_goal biframe s]

exception Not_FADUP_formula
exception Not_FADUP_iter

class check_fadup ~(cntxt:Constr.trace_cntxt) tau = object (self)

  inherit [Term.timestamp list] Iter.fold ~cntxt as super

  method check_formula f = ignore (self#fold_message [Term.mk_pred tau] f)

  method extract_ts_atoms phi =
    List.partition
      (function Term.Atom (`Timestamp _) -> true | _ -> false)
      (Term.decompose_ands phi)

  method add_atoms atoms timestamps =
    List.fold_left
      (fun acc at -> match at with
        | Term.Atom (`Timestamp (`Leq,tau_1,tau_2)) ->
          if List.mem tau_2 acc
          then tau_1::acc
          else acc
        | Atom (`Timestamp (`Lt,tau_1,tau_2)) ->
          if (List.mem (Term.mk_pred tau_2) acc || List.mem tau_2 acc)
          then tau_1::acc
          else acc
        | _ -> raise Not_FADUP_iter)
      timestamps
      atoms

  method fold_message timestamps t = match t with
    | Macro (ms,[],a)
      when (ms = Term.in_macro && (a = tau || List.mem a timestamps)) ||
           (ms = Term.out_macro && List.mem a timestamps) ->
      timestamps

    | Fun (f,_, [Macro (ms,[],a);then_branch; _])
      when f = Term.f_ite && ms = Term.exec_macro && List.mem a timestamps ->
      self#fold_message timestamps then_branch

    | Fun (f, _, [phi_1;phi_2]) when f = Term.f_impl ->
      let atoms,l = self#extract_ts_atoms phi_1 in
      let ts' = self#add_atoms atoms timestamps in
      List.iter
        (fun phi -> ignore (self#fold_message ts' phi))
        (phi_2::l) ;
      timestamps

    | Fun (f, _, _) when f = Term.f_and ->
      let atoms,l = self#extract_ts_atoms t in
      let ts' = self#add_atoms atoms timestamps in
      List.iter
        (fun phi -> ignore (self#fold_message ts' phi))
        l ;
      timestamps

    | Atom (`Index _) | Atom (`Timestamp _) -> timestamps

    | Fun _ | Seq _ | Find _
    | Atom (`Message _)
    | ForAll _ | Exists _ -> super#fold_message timestamps t

    | Macro _ | Name _ | Var _ | Diff _
    | Atom (`Happens _) -> raise Not_FADUP_iter
end

let fa_dup_int (i : int L.located) s =
  let before, e, after = split_equiv_goal i s in

  let biframe_without_e = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  try
    (* we expect that e is of the form exec@pred(tau) && phi *)
    let (tau,phi) =
      let f,g = match e with
        | Term.Fun (fs,_, [f;g]) when fs = Term.f_and -> f,g

        | Term.Seq (vars, Term.Fun (fs,_, [f;g])) when fs = Term.f_and ->
          let _, subst = Term.erefresh_vars `Global vars in
          Term.subst subst f,
          Term.subst subst g

        | _ -> raise Not_FADUP_formula
      in

      match f,g with
      | (Term.Macro (fm,[], Term.Pred tau), phi) when fm = Term.exec_macro
        -> (tau,phi)
      | (phi, Term.Macro (fm,[], Term.Pred tau)) when fm = Term.exec_macro
        -> (tau,phi)
      | _ -> raise Not_FADUP_formula
    in

    let frame_at_pred_tau =
      Term.mk_macro Term.frame_macro [] (Term.mk_pred tau)
    in
    (* we first check that frame@pred(tau) is in the biframe *)
    if not (List.mem frame_at_pred_tau biframe_without_e) then
      raise Not_FADUP_formula;

    (* we iterate over the formula phi to check if it contains only
     * allowed subterms *)
    let iter = new check_fadup ~cntxt tau in
    iter#check_formula phi ;
    (* on success, we keep only exec@pred(tau) *)
    let new_elem = Term.mk_macro Term.exec_macro [] (Term.mk_pred tau) in

    [ES.set_equiv_goal (List.rev_append before (new_elem::after)) s]

  with
  | Not_FADUP_formula ->
    soft_failure (Tactics.Failure "can only apply the tactic on \
                                   a formula of the form (exec@pred(tau) && phi) \
                                   with frame@pred(tau) in the biframe")

  | Not_FADUP_iter ->
    soft_failure (Tactics.Failure "the formula contains subterms \
                                   that are not handled by the FADUP rule")


let fadup Args.(Opt (Int, p)) s : ES.sequents =
  match p with
  | None -> fa_dup s
  | Some (Args.Int i) -> fa_dup_int i s

let () =
 T.register_typed "fadup"
   ~general_help:"When applied without argument, tries to remove all terms that \
                  are duplicates, or context of duplicates."
   ~detailed_help: "When applied on a formula of the form (exec@pred(tau) && \
                    phi), with frame@pred(tau) in the biframe, tries to remove \
                    phi if it contains only subterms allowed by the FA-DUP rule."
   ~tactic_group:Structural
   (LowTactics.genfun_of_pure_efun_arg fadup) Args.(Opt Int)



(*------------------------------------------------------------------*)
(** Macro occurrence utility functions *)

(** Return timestamps occuring in macros in a set of terms *)
let get_macro_actions
    (cntxt : Constr.trace_cntxt)
    (sources : Term.messages) : Fresh.ts_occs 
  =
  let actions = 
    List.concat_map (Fresh.get_actions_ext cntxt) sources
  in
  Fresh.clear_dup_mtso_le actions

(** [mk_le_ts_occ env ts0 occ] build a condition stating that [ts0] occurs 
    before the macro timestamp occurrence [occ]. *)
let mk_le_ts_occ
    (env : Vars.env)
    (ts0 : Term.timestamp) 
    (occ : Fresh.ts_occ) : Term.message
  =
  let occ_vars = Sv.elements occ.Iter.occ_vars in
  let occ_vars, occ_subst = Term.erefresh_vars (`InEnv (ref env)) occ_vars in
  let subst = occ_subst in
  let ts   = Term.subst subst occ.occ_cnt  in
  let cond = Term.subst subst occ.occ_cond in
  Term.mk_exists ~simpl:true occ_vars
    (Term.mk_and
       (Term.mk_timestamp_leq ts0 ts)
       cond)

let mk_le_ts_occs
    (env : Vars.env)
    (ts0 : Term.timestamp) 
    (occs : Fresh.ts_occs) : Term.messages 
  =
  List.map (mk_le_ts_occ env ts0) occs |> 
  List.remove_duplicate (=)

(*------------------------------------------------------------------*)
(** Fresh *)

let fresh_mk_direct
    (env : Vars.env)
    (n : Term.nsymb)
    (occ : Fresh.name_occ) : Term.message
  =
  let env = ref env in
  let bv, subst = Term.erefresh_vars (`InEnv env) (Sv.elements occ.occ_vars) in
  let cond = Term.subst subst occ.occ_cond in
  let j = List.map (Term.subst_var subst) occ.occ_cnt in
  Term.mk_forall ~simpl:true bv 
    (Term.mk_impl cond (Term.mk_indices_neq n.s_indices j))

let fresh_mk_indirect
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (n : Term.nsymb)
    (frame_actions : Fresh.ts_occs)
    (occ : TraceTactics.fresh_occ) : Term.message
  =
  (* for each action [a] in which [name] occurs with indices from [occ] *)
  let bv = occ.Iter.occ_vars in
  let action, occ = occ.Iter.occ_cnt in

  assert (Sv.subset (Action.fv_action action) (Sv.union (Vars.to_set env) bv));

  let env = ref env in
  let bv, subst = Term.erefresh_vars (`InEnv env) (Sv.elements bv) in

  (* apply [subst] to the action and to the list of
   * indices of our name's occurrences *)
  let action =
    SystemExpr.action_to_term cntxt.table cntxt.system
      (Action.subst_action subst action)
  in

  let occ = List.map (Term.subst_var subst) occ in

  (* environement with all new variables *)
  let env0 = !env in
  (* condition stating that [action] occurs before a macro timestamp 
     occurencing in the frame *)
  let disj = Term.mk_ors (mk_le_ts_occs env0 action frame_actions) in

  (* condition stating that indices of name in [action] and [name] differ *)
  let form = Term.mk_indices_neq occ n.s_indices in

  Term.mk_forall ~simpl:true bv (Term.mk_impl disj form)


(** Construct the formula expressing freshness for some projection. *)
let mk_phi_proj
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (n : Term.nsymb)
    (proj : Term.projection)
    (biframe : Term.message list) : Term.message list
  =
  let frame = List.map (Equiv.pi_term proj) biframe in
  try
    let frame_indices : Fresh.name_occs =
      List.fold_left (fun acc t ->
          Fresh.get_name_indices_ext cntxt n.s_symb t @ acc
        ) [] frame
    in
    let frame_indices = List.sort_uniq Stdlib.compare frame_indices in

    (* direct cases (for explicit occurrences of [name] in the frame) *)
    let phi_frame = List.map (fresh_mk_direct env n) frame_indices in

    let frame_actions : Fresh.ts_occs = get_macro_actions cntxt frame in

    let macro_cases = 
      TraceTactics.mk_fresh_indirect_cases cntxt env n biframe 
    in

    (* indirect cases (occurrences of [name] in actions of the system) *)
    let phi_actions =
      List.fold_left (fun forms (_, cases) ->
          let cases = 
            List.map 
              (fresh_mk_indirect cntxt env n frame_actions) 
              cases 
          in
          cases @ forms
        ) [] macro_cases
    in

    List.remove_duplicate (=) (phi_frame @ phi_actions)

  with
  | Fresh.Name_found ->
    soft_failure (Tactics.Failure "name not fresh")
  | Fresh.Var_found ->
    soft_failure
      (Failure "cannot apply fresh: the formula contains a term variable")

let fresh_cond (cntxt : Constr.trace_cntxt) env t biframe : Term.message =
  let n_left, n_right =
    match Term.pi_term PLeft t, Term.pi_term PRight t with
    | (Name nl, Name nr) -> nl, nr
    | _ -> raise Fresh.Not_name
  in

  let system_left = SE.project PLeft cntxt.system in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = mk_phi_proj cntxt_left env n_left PLeft biframe in

  let system_right = SE.project PRight cntxt.system in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = mk_phi_proj cntxt_right env n_right PRight biframe in

  Term.mk_ands
    (* remove duplicates, and then concatenate *)
    ((List.filter (fun x -> not (List.mem x phi_right)) phi_left)
     @
     phi_right)


(** Returns the term [if (phi_left && phi_right) then 0 else diff(nL,nR)]. *)
let fresh_mk_if_term (cntxt : Constr.trace_cntxt) env t biframe =
  if not Symbols.(check_bty_info cntxt.table (Term.ty t) Ty_large) then
    soft_failure
      (Failure "name is of a type that is not [large]");

  let phi = fresh_cond cntxt env t biframe in
  Term.mk_ite phi Term.mk_zero t


let fresh i s =
  let before, e, after = split_equiv_goal i s in

  (* the biframe to consider when checking the freshness *)
  let biframe = List.rev_append before after in
  (* expand the biframe to improve precision when computing the freshness
     condition *)
  let biframe_exp = List.map (fun t -> EquivLT.expand_all_term t s) biframe in
  let cntxt   = ES.mk_trace_cntxt s in
  let env     = ES.env s in
  try
    let if_term = fresh_mk_if_term cntxt env e biframe_exp in
    let biframe = List.rev_append before (if_term :: after) in
    [ES.set_equiv_goal biframe s]

  with Fresh.Not_name ->
    soft_failure
      (Tactics.Failure "Can only apply fresh tactic on names")

let fresh_tac args = match args with
  | [Args.Int_parsed i] -> wrap_fail (fresh i)
  | _ -> bad_args ()


(*------------------------------------------------------------------*)
(** Sequence expansion of the sequence [term] for the given parameters [ths]. *)
let expand_seq (term : Theory.term) (ths : Theory.term list) (s : ES.t) =
  let env = ES.env s in
  let table = ES.table s in
  match EquivLT.convert_i s term with
  (* we expect term to be a sequence *)
  | (Seq (vs, t) as term_seq), ty ->
    (* we parse the arguments ths, to create a substution for variables vs *)
    let subst = Theory.parse_subst table (ES.ty_vars s) env vs ths in

    (* new_t is the term of the sequence instantiated with the subst *)
    let new_t = Term.subst subst t in

    (* we add the new term to the frame and the hypothesis if it does not yet
       belongs to it *)
    let biframe =
      let old_biframe = ES.goal_as_equiv s in
      if List.mem new_t old_biframe then old_biframe else new_t :: old_biframe
    in

    let rec mk_hyp_f = function
      | Equiv.Atom at       -> Equiv.Atom (mk_hyp_at at)
      | Equiv.Impl (f, f0)  -> Equiv.Impl (mk_hyp_f f, mk_hyp_f f0)
      | _ as f -> f

    and mk_hyp_at hyp = match hyp with
      | Equiv.Equiv e ->
        let new_e =
          if not (List.mem new_t e) && List.mem term_seq e
          then new_t :: e
          else e
        in
        Equiv.Equiv new_e

      | Equiv.Reach f -> hyp
    in

    let s = Hyps.map mk_hyp_f s in

    [ ES.set_equiv_goal biframe s]

  | _ ->
    hard_failure
      (Tactics.Failure "can only expand with sequences with parameters")


(*------------------------------------------------------------------*)
let expand_seq args s =
  match args with
  | (Args.Theory v) :: ids ->
    let ids =
      List.map (function
          | Args.Theory th -> th
          | _ -> bad_args ()
        ) ids
    in
    expand_seq v ids s
  | _ -> bad_args ()

let expand_seq_tac args = wrap_fail (expand_seq args)

(* Does not rely on the typed registration, as it parses a substitution. *)
let () = T.register_general "expandseq"

    ~tactic_help:{general_help = "Expand the given sequence.";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Structural}
    (LowTactics.gentac_of_etac_arg expand_seq_tac)


(*------------------------------------------------------------------*)
(** Replace all occurrences of [t1] by [t2] inside of [s],
  * and add a subgoal to prove that [t1 <=> t2]. *)
let equiv_formula f1 f2 (s : ES.t) =
  (* goal for the equivalence of t1 and t2 *)
  let f =
    Term.mk_and ~simpl:false
      (Term.mk_impl ~simpl:false f1 f2)
      (Term.mk_impl ~simpl:false f2 f1)
  in
  let trace_sequent = ES.(to_trace_sequent (set_reach_goal f s)) in

  let subgoals =
    [ Goal.Trace trace_sequent;
      Goal.Equiv
        (ES.subst [Term.ESubst (f1,f2)] s) ]
  in
  subgoals

(** Replace all occurrences of [m1] by [m2] inside of [s],
  * and add a subgoal to prove that [Eq(m1, m2)]. *)
let equiv_message m1 m2 (s : ES.t) =
  (* goal for the equivalence of t1 and t2 *)
  let trace_sequent =
    ES.(to_trace_sequent
         (set_reach_goal (Term.mk_atom `Eq m1 m2) s))
  in
  let subgoals =
    [ Goal.Trace trace_sequent;
      Goal.Equiv
        (ES.subst [Term.ESubst (m1,m2)] s) ]
  in
  subgoals

(* TODO: subsumed by rewrite *)
let equivalent arg s = match arg with
  | Args.Pair (t1,t2) ->
    match t1, t2 with
    | Args.ETerm (ty1, f1, _), Args.ETerm (ty2, f2, _) ->
      match Type.kind ty1, Type.kind ty2 with
      | Type.KMessage, Type.KMessage when ty1 = ty2 ->
        (* TODO: subtypes: unify ty1 and ty2 *)
        if ty1 = Type.Boolean
        then equiv_formula f1 f2 s
        else equiv_message f1 f2 s

      | _ ->
        hard_failure
          (Tactics.Failure ("expected a pair of messages of the same types"))

let () = T.register_typed "equivalent"
    ~general_help:"Replace all occurrences of a formula by another, and ask to \
                   prove that they are equivalent."
    ~detailed_help:"This can be used on messages equality or formulas \
                    equivalence."
    ~tactic_group:Structural
    ~usages_sorts:[Args.(Sort (Pair (Message, Message)));
                   Args.(Sort (Pair (Boolean, Boolean)))]
    (LowTactics.genfun_of_efun_arg equivalent)
    Args.(Pair (ETerm, ETerm))


(*------------------------------------------------------------------*)
let simplify_ite b s cond positive_branch negative_branch =
  if b then
    (* replace in the biframe the ite by its positive branch *)
    (* ask to prove that the cond of the ite is True *)
    let trace_s = ES.(to_trace_sequent (set_reach_goal cond s)) in
    (positive_branch, trace_s)
  else
    (* replace in the biframe the ite by its negative branch *)
    (* ask to prove that the cond of the ite implies False *)
    let trace_s =
      ES.(to_trace_sequent
            (set_reach_goal (Term.mk_impl cond Term.mk_false) s)) in
    (negative_branch, trace_s)


let get_ite ~cntxt elem =
  match Iter.get_ite_term cntxt elem with
  | [] -> None
  | occ :: _ ->
    (* Context with bound variables (eg try find) are not supported. *)
    if not (Sv.is_empty occ.Iter.occ_vars) then
      soft_failure (Tactics.Failure "cannot be applied in a under a binder");

    Some (occ.Iter.occ_cnt)

let yes_no_if b i s =
  let cntxt = ES.mk_trace_cntxt s in

  let before, elem, after = split_equiv_goal i s in

  (* search for the first occurrence of an if-then-else in [elem] *)
  match get_ite ~cntxt elem with
  | None ->
    soft_failure
      (Tactics.Failure
         "can only be applied on a term with at least one occurrence \
          of an if-then-else term")

  | Some (c,t,e) ->
    let branch, trace_sequent = simplify_ite b s c t e in
    let new_elem =
      Equiv.subst_equiv
        [Term.ESubst (Term.mk_ite ~simpl:false c t e,branch)]
        [elem]
    in
    let biframe = List.rev_append before (new_elem @ after) in
    [ Goal.Trace trace_sequent;
      Goal.Equiv (ES.set_equiv_goal biframe s) ]

let yes_no_if_args b args s : Goal.t list =
    match args with
    | [Args.Int_parsed arg] -> yes_no_if b arg s
    | _ -> bad_args ()

(*------------------------------------------------------------------*)
exception Not_ifcond

(** Push the formula [f] in the message [term].
  * Goes under function symbol, diff, seq and find. If [j]=Some jj, will push
  * the formula only in the jth subterm of the then branch (if it exists,
  * otherwise raise an error). *)
let push_formula (j: 'a option) f term =
  let f_vars = Term.fv f in
  let not_in_f_vars vs = Sv.disjoint vs f_vars in

  let rec mk_ite m = match m with
    (* if c then t else e becomes if (f => c) then t else e *)
    | Term.Fun (fs,_,[c;t;e]) when fs = Term.f_ite ->
      Term.mk_ite ~simpl:false (Term.mk_impl ~simpl:false f c) t e

    (* m becomes if f then m else 0 *)
    | _ -> Term.mk_ite ~simpl:false f m Term.mk_zero
  in

  match term with
  | Term.Fun (f, _, _) when f = Term.f_ite -> mk_ite term

  | Term.Fun (f, fty, terms) ->
    begin match j with
      | None -> Term.mk_fun0 f fty (List.map mk_ite terms)
      | Some (Args.Int j) ->
        let loc, j = L.loc j, L.unloc j in
        if j < List.length terms then
          Term.mk_fun0 f fty
            (List.mapi (fun i t -> if i=j then mk_ite t else t) terms)
        else
          soft_failure ~loc
            (Tactics.Failure "out-of-bound position")
    end

  | Term.Diff (a, b) ->
    begin match j with
      | None -> Term.mk_diff (mk_ite a) (mk_ite b)
      | Some (Args.Int { L.pl_desc = 0}) -> Term.mk_diff (mk_ite a) b
      | Some (Args.Int { L.pl_desc = 1}) -> Term.mk_diff a (mk_ite b)
      | Some (Args.Int j) ->  
        soft_failure ~loc:(L.loc j)
          (Failure "expected value of 0 or 1 for diff terms")
    end

  | Term.Seq (vs, t) ->
    if not_in_f_vars (Sv.of_list vs) then Term.mk_seq0 vs (mk_ite t)
    else raise Not_ifcond

  | Term.Find (vs, b, t, e) ->
    if not_in_f_vars (Sv.of_list1 vs) then Term.mk_find vs b (mk_ite t) (mk_ite e)
    else raise Not_ifcond

  | _ -> mk_ite term

let ifcond Args.(Pair (Int i, Pair (Opt (Int, j), Boolean f))) s =
  let before, e, after = split_equiv_goal i s in

  let cond, positive_branch, negative_branch =
    match e with
    | Term.Fun (fs,_,[c;t;e]) when fs = Term.f_ite -> (c, t, e)
    | _ ->  soft_failure
              (Tactics.Failure "can only be applied to a conditional")
  in

  try
    let new_elem =
      Term.mk_ite ~simpl:false
        cond (push_formula j f positive_branch) negative_branch
    in
    let biframe = List.rev_append before (new_elem :: after) in
    let trace_sequent =
      ES.(to_trace_sequent
            (set_reach_goal Term.(mk_impl ~simpl:false cond f) s))
    in

    [ Goal.Trace trace_sequent;
      Goal.Equiv (ES.set_equiv_goal biframe s) ]
  with
  | Not_ifcond ->
    soft_failure
      (Tactics.Failure "the formula contains variables that overlap with \
                        variables bound by \
                        a seq or a try find construct")


let () =
  T.register_typed "ifcond"
    ~general_help: "If the given conditional implies that the given formula f is \
                    true, push the formula f at top-level in all the subterms of \
                    the then branch. "
    ~detailed_help:"A message m in the positive branch will become of the form \
                    `if f then m else 0`. If the int parameter j is given, will \
                    push the formula only in the jth subterm of the then branch \
                    (zero-based)."
   ~tactic_group:Structural
   (LowTactics.genfun_of_efun_arg ifcond) Args.(Pair (Int, Pair( Opt Int, Boolean)))


(*------------------------------------------------------------------*)
(* TODO: should be a rewriting rule *)
let trivial_if (Args.Int i) (s : ES.sequent) =
  let cntxt = ES.mk_trace_cntxt s in

  let before, elem, after = split_equiv_goal i s in

  (* search for the first occurrence of an if-then-else in [elem] *)
  match get_ite ~cntxt elem with
  | None ->
    soft_failure
      (Tactics.Failure
         "can only be applied on a term with at least one occurrence \
          of an if then else term")
  | Some (c,t,e) ->
    let trace_seq =
      ES.(to_trace_sequent
           (set_reach_goal (Term.mk_atom `Eq t e) s))
    in
    let trace_goal  = Goal.Trace trace_seq in

    let new_elem =
      Equiv.subst_equiv
        [Term.ESubst (Term.mk_ite c t e,t)]
        [elem]
    in
    let biframe = List.rev_append before (new_elem @ after) in
    [ trace_goal;
      Goal.Equiv (ES.set_equiv_goal biframe s) ]

let () =
 T.register_typed "trivialif"
   ~general_help:"Simplify a conditional when the two branches are equal."
   ~detailed_help:""
   ~tactic_group:Structural
   (LowTactics.genfun_of_efun_arg trivial_if) Args.Int


(*------------------------------------------------------------------*)
(* TODO: should be a rewriting rule *)
let ifeq Args.(Pair (Int i, Pair (Message (t1,ty1), Message (t2,ty2)))) s =

  (* check that types are equal *)
  EquivLT.check_ty_eq ty1 ty2;

  let before, e, after = split_equiv_goal i s in

  let cond, positive_branch, negative_branch =
    match e with
    | Term.Fun (fs,_,[c;t;e]) when fs = Term.f_ite -> (c, t, e)
    | _ -> soft_failure
             (Tactics.Failure "Can only be applied to a conditional.")
  in
  let new_elem =
    Term.mk_ite
      cond
      (Term.subst [Term.ESubst (t1,t2)] positive_branch)
      negative_branch
  in
  let biframe = List.rev_append before (new_elem :: after) in

  let trace_s =
    ES.(to_trace_sequent
          (set_reach_goal
             (Term.mk_impl ~simpl:false cond (Term.mk_atom `Eq t1 t2))
             s))
  in

  [ Goal.Trace trace_s;
    Goal.Equiv (ES.set_equiv_goal biframe s) ]

let () = T.register_typed "ifeq"
    ~general_help:"If the given conditional implies the equality of the two \
                   given terms, substitute the first one by the second one \
                   inside the positive branch of the conditional."

    ~detailed_help:"This asks to prove that the equality is indeed implied by \
                    the condition, we can then replace any term by its equal \
                    term (with over-whelming probability) in the positive \
                    brannch."
    ~tactic_group:Structural
    (LowTactics.genfun_of_efun_arg ifeq) Args.(Pair (Int, Pair (Message, Message)))


(*------------------------------------------------------------------*)
(** Automatic simplification *)

let goal_is_reach s =
  match ES.goal s with
  | Equiv.Atom (Reach _) -> true
  | _ -> false

let rec auto ~strong ~close s sk (fk : Tactics.fk) =
  let open Tactics in
  match s with
  | Goal.Trace t ->
    let sk l fk = sk (List.map (fun s -> Goal.Trace s) l) fk in
    TraceTactics.simpl ~close ~strong t sk fk

  | Goal.Equiv s when goal_is_reach s ->
    auto ~close ~strong (byequiv s) sk fk

  | Goal.Equiv s ->
    let sk l _ =
      sk (List.map (fun s -> Goal.Equiv s) l) fk
    and fk _ =
      if close
      then fk (None, GoalNotClosed)
      else sk [Equiv s] fk
    in

    let wfadup s sk fk =
      if strong || (Config.auto_fadup ()) then
        let fk _ = sk [s] fk in
        wrap_fail (fadup (Args.Opt (Args.Int, None))) s sk fk
      else sk [s] fk
    in

    let conclude s sk fk  =
      if close || Config.auto_intro () then
        let fk = if Config.auto_intro () then fun _ -> sk [s] fk else fk in
        andthen_list ~cut:true
          [wrap_fail (EquivLT.expand_all_l `All);
           try_tac wfadup;
           orelse_list [wrap_fail refl_tac;
                        wrap_fail assumption]] s sk fk
      else sk [s] fk
    in

    let reduce s sk fk =
      if strong
      then sk [EquivLT.reduce_sequent Reduction.{ delta = false } s] fk
      else sk [s] fk
    in

    andthen_list ~cut:true
      [try_tac reduce;
       try_tac wfadup;
       conclude]
      s sk fk

let tac_auto ~close ~strong args s sk (fk : Tactics.fk) =
  match args with
  | [] -> auto ~close ~strong s sk fk
  | _ -> hard_failure (Tactics.Failure "no argument allowed")

let tac_autosimpl s = tac_auto ~close:false ~strong:false s
  

(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** PRF axiom *)

type prf_param = {
  h_fn  : Term.fname;   (** function name *)
  h_fty : Type.ftype;   (** Hash function type *)
  h_cnt : Term.message; (** contents, i.e. hashed message *)
  h_key : Term.nsymb;   (** key *)
}

let prf_param hash : prf_param =
  match hash with
  | Term.Fun ((h_fn, _), h_fty, [h_cnt; Name h_key]) ->
    { h_fn; h_cnt; h_fty; h_key }

  | _ -> soft_failure Tactics.Bad_SSC

(** Compute conjunct of PRF condition for a direct case,
  * that is an explicit occurrence of the hash in the frame. *)
let prf_mk_direct env (param : prf_param) (occ : Iter.hash_occ) =
  (* select bound variables in key indices [is] and in message [m]
     to quantify universally over them *)
  let env = ref env in

  let vars = occ.occ_vars in

  let vars, subst = Term.erefresh_vars (`InEnv env) (Sv.elements vars) in

  let is, m = occ.occ_cnt in
  let is = List.map (Term.subst_var subst) is in
  let m = Term.subst subst m in
  (* let cond = Term.subst subst occ.occ_cond in *)
  let cond = Term.mk_true in
  Term.mk_forall ~simpl:true
    vars
    (Term.mk_impl
       (Term.mk_and ~simpl:true
          cond
          (Term.mk_indices_eq param.h_key.s_indices is))
       (Term.mk_atom `Neq param.h_cnt m))

(*------------------------------------------------------------------*)
(** triple of the action, the key indices and the term *)
type prf_occ = (Action.action * Vars.index list * Term.message) Iter.occ

(** check if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name *)
let prf_occ_incl table system (o1 : prf_occ) (o2 : prf_occ) : bool = 
  let a1, is1, t1 = o1.occ_cnt in
  let a2, is2, t2 = o2.occ_cnt in

  let cond1, cond2 = o1.occ_cond, o2.occ_cond in

  (* build a dummy term, which we used to match in one go all elements of
     the two occurrences *)
  let mk_dum a is cond t =
    let action = SE.action_to_term table system a in
    Term.mk_ands ~simpl:false
      ((Term.mk_atom `Eq Term.init action) ::
       (Term.mk_indices_eq ~simpl:false is is) ::
       cond ::
       [Term.mk_atom `Eq t (Term.mk_witness (Term.ty t))])
  in
  let pat2 = Match.{
      pat_tyvars = [];
      pat_vars   = o2.occ_vars;
      pat_term   = mk_dum a2 is2 cond2 t2;
    }
  in

  match Match.T.try_match_term table system (mk_dum a1 is1 cond1 t1) pat2 with
  | Match.FreeTyv | Match.NoMatch _ -> false
  | Match.Match _ -> true

(** Compute conjunct of PRF condition for an indirect case,
  * that is an occurence of the hash in actions of the system. *)
let prf_mk_indirect
    (env           : Vars.env)
    (cntxt         : Constr.trace_cntxt)
    (param         : prf_param)
    (frame_actions : Fresh.ts_occs)
    (hash_occ      : prf_occ) : Term.message
  =
  let env = ref env in

  let vars = Sv.elements hash_occ.Iter.occ_vars in
  let vars, subst = Term.erefresh_vars (`InEnv env) vars in

  let action, hash_is, hash_m = hash_occ.Iter.occ_cnt in

  (* apply [subst] to the action and to the list of
   * key indices with the hashed messages *)
  let action =
    SE.action_to_term cntxt.table cntxt.system
      (Action.subst_action subst action)
  in
  let hash_is = List.map (Term.subst_var subst) hash_is
  and hash_m = Term.subst subst hash_m
  and hash_cond = Term.subst subst hash_occ.Iter.occ_cond in

  (* save the environment after having renamed all free variables until now. *)
  let env0 = !env in
  (* condition stating that [action] occurs before a macro timestamp 
     occurencing in the frame *)
  let disj = Term.mk_ors (mk_le_ts_occs env0 action frame_actions) in

  (* then if key indices are equal then hashed messages differ *)
  let form =
    Term.mk_impl
      (Term.mk_and ~simpl:true
         hash_cond
         (Term.mk_indices_eq param.h_key.s_indices hash_is))
      (Term.mk_atom `Neq param.h_cnt hash_m)
  in

  Term.mk_forall ~simpl:true vars (Term.mk_impl disj form)

(*------------------------------------------------------------------*)
(** indirect case in a PRF application: PRF hash occurrence, sources *)
type prf_case = prf_occ * Term.message list

(** map from action names to PRF cases *)
type prf_cases_sorted = (Symbols.action Symbols.t * prf_case list) list

let add_prf_case
    table system
    (action_name : Symbols.action Symbols.t)
    (c : prf_case)
    (assoc_cases : prf_cases_sorted) : prf_cases_sorted 
  =
  let add_case (c : prf_case) (cases : prf_case list) : prf_case list =
    let occ, srcs = c in

    (* look if [c] is subsumed by one of the element [c2] of [cases], 
       in which case we update the possible sources of [c2] (note 
       that this causes some loss of precision)  *)
    let found = ref false in
    let new_cases =
      List.fold_right (fun ((occ', srcs') as c2) cases ->
          if (not !found) && prf_occ_incl table system occ occ' then
            let () = found := true in
            (occ', srcs @ srcs') :: cases 
          else c2 :: cases
        ) cases []
    in
    if !found 
    then List.rev new_cases 
    else c :: cases
    (* we cannot remove old cases which are subsumed by [c], because 
       we also need to handle sources *)
  in

  List.assoc_up_dflt action_name [] (add_case c) assoc_cases

(*------------------------------------------------------------------*)
let mk_prf_phi_proj cntxt env param frame hash =
  (* Check syntactic side condition. *)
  let errors =
    Euf.key_ssc
      ~elems:frame ~allow_functions:(fun x -> false)
      ~cntxt param.h_fn param.h_key.s_symb
  in
  if errors <> [] then
    soft_failure (Tactics.BadSSCDetailed errors);

  (* Direct cases: hashes from the frame. *)

  let frame_hashes : Iter.hash_occs =
    List.fold_left (fun acc t ->
        Iter.get_f_messages_ext ~cntxt param.h_fn param.h_key.s_symb t @ acc
      ) [] frame
  in
  let frame_hashes = List.sort_uniq Stdlib.compare frame_hashes in
  let phi_direct =
    List.map (prf_mk_direct env param) frame_hashes
  in

  (* Indirect cases: potential occurrences through macro expansions. *)

  (** Compute association list from action names to prf cases. *)
  let macro_cases : prf_cases_sorted =
    Iter.fold_macro_support (fun iocc macro_cases ->
        let name = iocc.iocc_aname in
        let t = iocc.iocc_cnt in
        let fv = Sv.diff (Term.fv t) (Vars.to_set env) in

        let new_cases =
          Iter.get_f_messages_ext ~fv ~cntxt param.h_fn param.h_key.s_symb t
        in
        let new_cases = 
          List.map (fun occ -> 
              let is, t = occ.Iter.occ_cnt in
              Iter.{ occ with occ_cnt = (iocc.iocc_action, is, t) }
            ) new_cases
        in

        List.fold_left (fun macro_cases new_case ->
            add_prf_case cntxt.table cntxt.system
              name (new_case, iocc.iocc_sources) macro_cases
          ) macro_cases new_cases
      ) cntxt env frame []
  in
  (* Keep only actions in which there is at least one occurrence. *)
  let macro_cases = List.filter (fun (_, occs) -> occs <> []) macro_cases in

  let phi_indirect =
    List.map (fun (action, hash_occs) ->
        List.map (fun (hash_occ, srcs) -> 
            let frame_actions = get_macro_actions cntxt srcs in
            prf_mk_indirect env cntxt param frame_actions hash_occ 
          ) (List.rev hash_occs)
      ) (List.rev macro_cases)
  in
  let phi_indirect = List.flatten phi_indirect in

  Term.mk_ands ~simpl:true phi_direct, Term.mk_ands ~simpl:true phi_indirect


(** Build the PRF condition on one side, if the hash occurs on this side.
    Return [None] if the hash does not occurs. *)
let prf_condition_side
    (proj : Term.projection)
    (cntxt : Constr.trace_cntxt) 
    (env : Vars.env) 
    (biframe : Equiv.equiv)
    (e : Term.message)
    (hash : Term.message) : (Term.form * Term.form) option
  =
  let exception HashNoOcc in
  try
    let cntxt = { cntxt with system = SE.project proj cntxt.system } in
    let param = prf_param (Term.pi_term proj hash) in

    (* Create the frame on which we will iterate to compute the PRF formulas *)
    let hash_ty = param.h_fty.fty_out in
    let v = Vars.make_new hash_ty "v" in

    let e_without_hash =
      Term.subst [Term.ESubst (hash,Term.mk_var v)] e
    in
    let e_without_hash = Term.pi_term proj e_without_hash in

    (* [hash] does not appear on this side *)
    if not (Sv.mem (Vars.EVar v) (Term.fv e_without_hash)) then
      raise HashNoOcc;

    let e_without_hash = 
      Term.subst
        [Term.ESubst (Term.mk_var v, Term.mk_witness hash_ty)]
        e_without_hash 
    in

    let frame =
      param.h_cnt :: e_without_hash :: List.map (Equiv.pi_term proj) (biframe)
    in
    Some (mk_prf_phi_proj cntxt env param frame hash)

  with
  | HashNoOcc -> None

(* From two conjunction formulas p and q, produce a minimal diff(p, q),
 * of the form (p inter q) && diff (p minus q, q minus p). *)
let combine_conj_formulas p q =
  (* Turn the conjunctions into lists. *)
  let p, q = Term.decompose_ands p, Term.decompose_ands q in
  let aux_q = ref q in
  let (common, new_p) = List.fold_left (fun (common, r_p) p ->
      (* If an element of p is inside aux_q, remove it from aux_q and
       * add it to common, else add it to r_p. *)
      if List.mem p !aux_q then
        (aux_q := List.filter (fun e -> e <> p) !aux_q; (p::common, r_p))
      else
        (common, p::r_p))
      ([], []) p
  in
  (* [common] is the intersection of p and q,
   * [aux_q] is the remainder of q and
   * [new_p] the remainder of p. *)
  Term.mk_and
    (Term.mk_ands common)
    (Term.head_normal_biterm
       (Term.mk_diff (Term.mk_ands new_p) (Term.mk_ands (List.rev !aux_q))))

(** Application of PRF tactic on biframe element number i,
  * optionally specifying which subterm m1 should be considered. *)
let prf Args.(Pair (Int i, Opt (Message, m1))) s =
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let env = ES.env s in

  let e = Term.head_normal_biterm e in
  (* search for the first occurrence of a hash in [e] *)
  let hash_occ =
    match Iter.get_ftypes (ES.table s) Symbols.Hash e, m1 with
    | [], _ ->
      soft_failure
        (Tactics.Failure
           "PRF can only be applied on a term with at least one occurrence \
            of a hash term h(t,k)")

    | occ :: _, None ->
      if not (Sv.is_empty occ.Iter.occ_vars) then
        soft_failure
          (Tactics.Failure "application below a binder is not supported");
      occ

    | occs, Some (Message (hash, _)) ->
      begin match
        List.find (fun hash_occ -> hash_occ.Iter.occ_cnt = hash) occs
      with
        | occ -> occ
        | exception Not_found ->
          soft_failure
            (Tactics.Failure "the given hash does not occur in the term")
      end
  in
  let fn, ftyp, m, key, hash = match hash_occ.Iter.occ_cnt with
    | Term.Fun ((fn,_), ftyp, [m; key]) as hash ->
      fn, ftyp, m, key, hash
    | _ -> assert false
  in

  (* The formula, without the oracle condition. *)
  let formula =
    let cond_l = prf_condition_side PLeft  cntxt env biframe e hash 
    and cond_r = prf_condition_side PRight cntxt env biframe e hash in

    match cond_l, cond_r with
    | None, None -> assert false

    (* the hash occurs only on one side *)
    | Some (direct, indirect), None
    | None, Some (direct, indirect) ->
      Term.mk_and ~simpl:false direct indirect

      (* the hash occurs on both side *)
    | Some (direct_l, indirect_l), Some (direct_r, indirect_r) ->
      Term.mk_and ~simpl:false
        (combine_conj_formulas   direct_l   direct_r)
        (combine_conj_formulas indirect_l indirect_r)
  in

  (* Check that there are no type variables. *)
  assert (ftyp.fty_vars = []);

  let nty = ftyp.fty_out in
  let ndef = Symbols.{ n_iarr = 0; n_ty = nty; } in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_PRF") ndef
  in
  let ns = Term.mk_isymb n nty [] in
  let s = ES.set_table table s in

  let oracle_formula =
    Prover.get_oracle_tag_formula (Symbols.to_string fn)
  in

  let final_if_formula =
    if Term.is_false oracle_formula then formula else
      let (Vars.EVar uvarm),(Vars.EVar uvarkey),f =
        match oracle_formula with
        | ForAll ([uvarm;uvarkey],f) -> uvarm,uvarkey,f
        | _ -> assert false
      in
      match Vars.ty uvarm, Vars.ty uvarkey with
      | Type.(Message, Message) ->
        let f =
          Term.subst [
            ESubst (Term.mk_var uvarm, m);
            ESubst (Term.mk_var uvarkey, key);] f
        in

        Term.mk_and (Term.mk_not f) formula

      | _ -> assert false
  in

  let if_term = Term.mk_ite final_if_formula (Term.mk_name ns) hash in
  let new_elem =
    Equiv.subst_equiv [Term.ESubst (hash,if_term)] [e]
  in
  let biframe = (List.rev_append before (new_elem @ after)) in
  [ES.set_equiv_goal biframe s]

let () =
  T.register_typed "prf"
    ~general_help:"Apply the PRF axiom."
    ~detailed_help:"It allows to replace a hash h(m,k) by 'if new_hash(m) then \
                    zero else h(m,k)' where new_hash(m) states that m \
                    was never hashed using key k before. Behaves similarly to \
                    the fresh tactic."
    ~tactic_group:Cryptographic
    (LowTactics.genfun_of_pure_efun_arg prf)
    Args.(Pair(Int, Opt Message))


(*------------------------------------------------------------------*)
let split_seq (li : int L.located) ht s : ES.sequent =
  let before, t, after = split_equiv_goal li s in
  let i = L.unloc li in

  let is, ti = match t with
    | Seq (is, ti) -> is, ti
    | _ ->
      soft_failure ~loc:(L.loc li) (Failure (string_of_int i ^ " is not a seq"))
  in

  (* check that types are compatible *)
  let seq_hty =
    Type.Lambda (List.map (fun v -> Vars.ety v) is, Type.Boolean)
  in

  let hty, ht = EquivLT.convert_ht s ht in

  EquivLT.check_hty_eq hty seq_hty;

  (* compute the new sequent *)
  let is, subst = Term.erefresh_vars `Global is in
  let ti = Term.subst subst ti in

  let is_terms = 
    List.map (fun (Vars.EVar v) -> Term.ETerm (Term.mk_var v)) is 
  in

  let cond = 
    match Term.apply_ht ht is_terms with
    | Term.Lambda ([], cond) -> cond
    | _ -> assert false
  in

  (* The value of the else branch is choosen depending on the type *)
  let else_branch = match Term.ty ti with
    | Type.Message -> Term.mk_zero
    | Type.Boolean -> Term.mk_false
    | ty -> Term.mk_witness ty
  in

  let ti_t = Term.mk_ite cond               ti else_branch in
  let ti_f = Term.mk_ite (Term.mk_not cond) ti else_branch in

  let env = ES.env s in
  let frame = List.rev_append before ([Term.mk_seq env is ti_t;
                                       Term.mk_seq env is ti_f] @ after) in
  ES.set_equiv_goal frame s

let split_seq_args args s : ES.sequent list =
  match args with
  | [Args.SplitSeq (i, ht)] -> [split_seq i ht s]
  | _ -> bad_args ()

let split_seq_tac args = wrap_fail (split_seq_args args) 

let () =
  T.register_general "splitseq"
    ~tactic_help:{general_help = "splits a sequence according to some boolean";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (LowTactics.gentac_of_etac_arg split_seq_tac)

(*------------------------------------------------------------------*)
let mem_seq (i_l : int L.located) (j_l : int L.located) s : Goal.t list =  
  let before, t, after = split_equiv_goal i_l s in
  let _, seq, _ = split_equiv_goal j_l s in

  let seq_vars, seq_term = match seq with
    | Seq (vs, t) -> vs, t
    | _ ->
      soft_failure ~loc:(L.loc j_l)
        (Failure (string_of_int (L.unloc j_l) ^ " is not a seq"))
  in

  EquivLT.check_ty_eq (Term.ty t) (Term.ty seq_term);

  (* refresh the sequence *)
  let env = ref (ES.env s) in
  let seq_vars, subst = Term.erefresh_vars (`InEnv env) seq_vars in
  let seq_term = Term.subst subst seq_term in

  let subgoal = 
    let form = 
      Term.mk_exists ~simpl:true seq_vars
        (Term.mk_atom `Eq t seq_term) 
    in
    let trace_s = ES.to_trace_sequent (ES.set_reach_goal form s) in
    Goal.Trace trace_s
  in

  let frame = List.rev_append before after in
  [subgoal; Goal.Equiv (ES.set_equiv_goal frame s)]

let mem_seq_args args s : Goal.t list =
  match args with
  | [Args.MemSeq (i, j)] -> mem_seq i j s
  | _ -> bad_args ()

let mem_seq_tac args = wrap_fail (mem_seq_args args) 

let () =
  T.register_general "memseq"
    ~tactic_help:{general_help = "prove that an biframe element appears in a \
                                 sequence of the biframe.";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (LowTactics.genfun_of_efun_arg mem_seq_tac)

(*------------------------------------------------------------------*)
(** implement the ConstSeq rule of CSF'21 *)
let const_seq
    ((li, b_t_terms) : int L.located * (Theory.hterm * Theory.term) list)
    (s : ES.t) : Goal.t list 
  =
  let before, e, after = split_equiv_goal li s in
  let i = L.unloc li in

  let e_is, e_ti = match e with
    | Seq (is, ti) -> is, ti
    | _ ->
      soft_failure ~loc:(L.loc li) (Failure (string_of_int i ^ " is not a seq"))
  in
  let b_t_terms =
    List.map (fun (p_bool, p_term) ->
        let b_ty,  t_bool = EquivLT.convert_ht s p_bool in
        let term, term_ty = EquivLT.convert_i s p_term in
        let p_bool_loc = L.loc p_bool in

        (* check that types are compatible *)
        let seq_hty =
          Type.Lambda (List.map (fun v -> Vars.ety v) e_is, Type.Boolean)
        in
        EquivLT.check_hty_eq ~loc:p_bool_loc b_ty seq_hty;
 
        EquivLT.check_ty_eq ~loc:(L.loc p_term) term_ty (Term.ty e_ti);

        (* check that [p_bool] is a pure timestamp formula *)
        let t_bool_body = match t_bool with
          | Term.Lambda (_, body) -> body
        in
        if not (Term.is_pure_timestamp t_bool_body) then
          hard_failure ~loc:p_bool_loc (Failure "not a pure timestamp formula");

        t_bool, term
      ) b_t_terms
  in

  (* refresh variables *)
  let env = ref (ES.env s) in
  let e_is, subst = Term.erefresh_vars (`InEnv env) e_is in
  let e_ti = Term.subst subst e_ti in

  (* instantiate all boolean [hterms] in [b_t_terms] using [e_is] *)
  let e_is_terms = 
    List.map (fun (Vars.EVar v) -> Term.ETerm (Term.mk_var v)) e_is 
  in
  let b_t_terms : (Term.message * Term.message) list =
    List.map (fun (t_bool, term) ->
        let t_bool = 
          match Term.apply_ht t_bool e_is_terms with
          | Term.Lambda ([], cond) -> cond
          | _ -> assert false
        in
        t_bool, term
      ) b_t_terms
  in

  (* first sub-goal: (∀ e_is, ∨ᵢ bᵢ *)
  let cases = Term.mk_ors ~simpl:true (List.map fst b_t_terms) in
  let cond1 =
    Term.mk_forall ~simpl:true e_is cases
  in
  let subg1 = ES.set_reach_goal cond1 s |> ES.to_trace_sequent in
  
  (* second sub-goal: (∧ᵢ (∀ e_is, bᵢ → tᵢ = e_ti) *)
  let eqs = List.map (fun (t_bool, term) ->
      Term.mk_forall ~simpl:true e_is
        (Term.mk_impl t_bool (Term.mk_atom `Eq e_ti term))
    ) b_t_terms
  in
  let cond2 = Term.mk_ands ~simpl:true eqs in
  let subg2 = ES.set_reach_goal cond2 s |> ES.to_trace_sequent in

  (* third sub-goal *)
  let terms = List.map snd b_t_terms in
  let frame = List.rev_append before (terms @ after) in

  [ Goal.Trace subg1;
    Goal.Trace subg2;
    Goal.Equiv (ES.set_equiv_goal frame s) ]

let const_seq_args args s : Goal.t list =
  match args with
  | [Args.ConstSeq (i, t)] -> const_seq (i, t) s
  | _ -> bad_args ()

let const_seq_tac args = wrap_fail (const_seq_args args) 

let () =
  T.register_general "constseq"
    ~tactic_help:{general_help = "simplifies a constant sequence";
                  detailed_help = "";
                  usages_sorts = [];
                  tactic_group = Logical}
    (LowTactics.genfun_of_efun_arg const_seq_tac)

(*------------------------------------------------------------------*)
(** Symmetric encryption **)


(** CCA1 *)

let cca1 Args.(Int i) s =
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.env s in

  let e = Term.head_normal_biterm e in

  let get_subst_hide_enc enc fnenc m fnpk sk fndec r eis is_top_level 
    : Goal.t * Term.esubst 
    =
    (* we check that the random is fresh, and the key satisfy the
       side condition. *)

    (* we create the fresh cond reachability goal *)
    let fresh_goal : Goal.t = 
      let form = fresh_cond cntxt env (Term.mk_name r) biframe in
      let seq = ES.to_trace_sequent (ES.set_reach_goal form s) in
      Goal.Trace seq
    in

    let new_subst : Term.esubst =
      if is_top_level then
        Term.ESubst (enc, Term.mk_len m)
      else
        let new_m = Term.mk_zeroes (Term.mk_len m) in
        let enc_sk = 
          match fnpk with
          | Some (fnpk,pkis) ->
            Term.mk_fun table fnpk pkis [Term.mk_name sk]

          | None -> Term.mk_name sk
        in
        let new_term = 
          Term.mk_fun table fnenc eis [new_m; Term.mk_name r; enc_sk]
        in
        Term.ESubst (enc, new_term)
    in
    (fresh_goal, new_subst)
  in

  (* if the term is an encryption at top level:
     - then, we will replace the encryption by the plaintext's length
     - else, we will replace the plaintext by its length *)
  let is_top_level : bool =
    match e with
    | Term.Fun ((fnenc,eis), _,
                [m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when (Symbols.is_ftype fnpk Symbols.PublicKey cntxt.table
            && Symbols.is_ftype fnenc Symbols.AEnc table) -> true

    | Term.Fun ((fnenc,eis), _, [m; Term.Name r; Term.Name sk])
      when Symbols.is_ftype fnenc Symbols.SEnc table -> true

    | _ -> false
  in

  (* search for the first occurrence of an asymmetric encryption in [e], that
     do not occur under a decryption symbol. *)
  (* FIXME: Adrien: the description is not accurrate *)
  let hide_all_encs (occ : Iter.mess_occ) : Goal.t * Term.esubst =
    (* FIXME: check that this is what we want. *)
    if not (Sv.is_empty occ.Iter.occ_vars) then
      soft_failure (Tactics.Failure "cannot be applied in a under a binder");

    match occ.Iter.occ_cnt with
    | (Term.Fun ((fnenc,eis), _,
                 [m; Term.Name r;
                  Term.Fun ((fnpk,is), _, [Term.Name sk])])
       as enc)
      when (Symbols.is_ftype fnpk Symbols.PublicKey table
            && Symbols.is_ftype fnenc Symbols.AEnc table) ->
      begin
        match Symbols.Function.get_data fnenc table with
        (* we check that the encryption function is used with the associated
           public key *)
        | Symbols.AssociatedFunctions [fndec; fnpk2] when fnpk2 = fnpk
          ->
          begin
            let errors =
              Euf.key_ssc ~messages:[enc] ~allow_functions:(fun x -> x = fnpk)
                ~cntxt fndec sk.s_symb
            in
            if errors <> [] then
              soft_failure (Tactics.BadSSCDetailed errors);

            if not (List.mem
                      (Term.mk_fun table fnpk is [Term.mk_name sk])
                      biframe) then
              soft_failure
                (Tactics.Failure
                   "The public key must be inside the frame in order to \
                    use CCA1");

            get_subst_hide_enc
              enc fnenc m (Some (fnpk,is))
              sk fndec r eis is_top_level
          end

        | _ ->
          soft_failure
            (Tactics.Failure
               "The first encryption symbol is not used with the correct \
                public key function.")
      end

    | (Term.Fun ((fnenc,eis), _, [m; Term.Name r; Term.Name sk])
       as enc) when Symbols.is_ftype fnenc Symbols.SEnc table
      ->
      begin
        match Symbols.Function.get_data fnenc table with
        (* we check that the encryption function is used with the associated
           public key *)
        | Symbols.AssociatedFunctions [fndec]
          ->
          begin
            try
              Cca.symenc_key_ssc ~elems:(ES.goal_as_equiv s) ~messages:[enc]
                ~cntxt fnenc fndec sk.s_symb;
              (* we check that the randomness is ok in the system and the
                 biframe, except for the encryptions we are looking at, which
                 is checked by adding a fresh reachability goal. *)
              Cca.symenc_rnd_ssc ~cntxt env fnenc sk biframe;
              get_subst_hide_enc enc fnenc m (None) sk fndec r eis is_top_level

            with Cca.Bad_ssc ->  soft_failure Tactics.Bad_SSC
          end
        | _ ->
          soft_failure
            (Tactics.Failure
               "The first encryption symbol is not used with the correct public \
                key function.")
      end

    | _ ->
      soft_failure
        (Tactics.Failure
           "CCA1 can only be applied on a term with at least one occurrence \
            of an encryption term enc(t,r,pk(k))")
  in

  let rec hide_all_encs_list
      (occs : Iter.mess_occs) : Goal.t list * Term.subst
    =
    match occs with
    | [] -> [], []
    | occ :: occs ->
      let fgoal,subst = hide_all_encs occ in
      let fgoals, substs = hide_all_encs_list occs in
      fgoal :: fgoals, subst :: substs
  in

  let fgoals, substs =
    hide_all_encs_list
      ((Iter.get_ftypes ~excludesymtype:Symbols.ADec table Symbols.AEnc e)
       @ (Iter.get_ftypes ~excludesymtype:Symbols.SDec table Symbols.SEnc e))
  in

  if substs = [] then
    soft_failure
      (Tactics.Failure
         "CCA1 can only be applied on a term with at least one occurrence \
          of an encryption term enc(t,r,pk(k))");

  let new_elem =    Equiv.subst_equiv substs [e] in
  let biframe = (List.rev_append before (new_elem @ after)) in
  Goal.Equiv (ES.set_equiv_goal biframe s) :: fgoals


let () =
  T.register_typed "cca1"
   ~general_help:"Apply the cca1 axiom on all encryptions of the given message."
   ~detailed_help:"Whenever an encryption does not occur under a decryption \
                   symbol and uses a valid fresh random, we can specify that it \
                   hides the message.
                   Encryption at toplevel are replaced by the length of the \
                   plaintext. Encryption not at toplevel are replaced by the \
                   encryption of the length of the plaintexts."
   ~tactic_group:Cryptographic
   (LowTactics.genfun_of_efun_arg cca1) Args.Int

(*------------------------------------------------------------------*)
(** Encryption key privacy  *)

let enckp
  Args.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2))))
  s =
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.env s in

  (* Apply tactic to replace key(s) in [enc] using [new_key].
   * Precondition:
   * [enc = Term.Fun ((fnenc,indices), [m; Term.Name r; k])].
   * Verify that the encryption primitive is used correctly,
   * that the randomness is fresh and that the keys satisfy their SSC. *)
  let apply
      ~(enc     : Term.message)
      ~(new_key : Term.message option)
      ~(fnenc   : Term.fname)
      ~(indices : 'a)
      ~(m       : 'b)
      ~(r       : Term.nsymb)
      ~(k       : Term.message)
    : Goal.t list =

    let k = Term.head_normal_biterm k in
    (* Verify that key is well-formed, depending on whether the encryption is
     * symmetric or not. Return the secret key and appropriate SSC. *)
    let ssc, wrap_pk, sk =
      if Symbols.is_ftype fnenc Symbols.SEnc table then
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             Cca.symenc_key_ssc
               ~cntxt fnenc fndec
               ~elems:(ES.goal_as_equiv s) sk.Term.s_symb;
             Cca.symenc_rnd_ssc ~cntxt env fnenc sk biframe;
             ()
          ),
          (fun x -> x),
          k
        | _ -> assert false

      else
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec;fnpk] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             let errors =
               Euf.key_ssc ~cntxt ~elems:(ES.goal_as_equiv s)
                 ~allow_functions:(fun x -> x = fnpk) fndec sk.s_symb
             in
             if errors <> [] then
               soft_failure (Tactics.BadSSCDetailed errors)),
          (fun x -> Term.mk_fun table fnpk indices [x]),
          begin match k with
            | Term.Fun ((fnpk',indices'), _, [sk])
              when fnpk = fnpk' && indices = indices' -> sk
            | Term.Fun ((fnpk',indices'), _, [sk])
              when fnpk = fnpk' && indices = indices' -> sk
            | _ ->
              soft_failure
                (Tactics.Failure
                   "The first encryption is not used \
                    with the correct public key function")
          end
        | _ -> assert false

    in
    let project = function
      | Term.Name n -> n,n
      | Term.(Diff (Name l, Name r)) -> l,r
      | _ -> soft_failure (Tactics.Failure "Secret keys must be names")
    in

    let skl, skr = project sk in
    let (new_skl, new_skr), new_key =
      match new_key with
      | Some k -> project k, k
      | None -> (skl, skl), Term.mk_name skl
    in

    EquivLT.check_ty_eq (Term.ty new_key) (Term.ty sk);

    (* Verify all side conditions, and create the reachability goal
     * for the freshness of [r]. *)
    let random_fresh_cond =
      try
        (* For each key we actually only need to verify the SSC
         * wrt. the appropriate projection of the system. *)
        let sysl = SystemExpr.(project PLeft cntxt.system) in
        let sysr = SystemExpr.(project PRight cntxt.system) in
        List.iter ssc
          (List.sort_uniq Stdlib.compare
             [(skl, sysl); (skr, sysr); (new_skl, sysl); (new_skr, sysr)]) ;
        let context =
          Equiv.subst_equiv [Term.ESubst (enc,Term.empty)] [e]
        in
        fresh_cond cntxt env (Term.mk_name r) (context@biframe)
      with Cca.Bad_ssc -> soft_failure Tactics.Bad_SSC
    in
    let fresh_goal =
      s |> ES.set_reach_goal random_fresh_cond |> ES.to_trace_sequent in

    (* Equivalence goal where [enc] is modified using [new_key]. *)
    let new_enc =
      Term.mk_fun table fnenc indices [m; Term.mk_name r; wrap_pk new_key]
    in
    let new_elem =
      Equiv.subst_equiv [Term.ESubst (enc,new_enc)] [e]
    in
    let biframe = (List.rev_append before (new_elem @ after)) in

    [Goal.Trace fresh_goal;
     Goal.Equiv (ES.set_equiv_goal biframe s)]

  in

  let target,new_key = match m1,m2 with
    | Some (Message (m1, _)), Some (Message (m2, _)) ->
      Some m1, Some m2

    | Some (Message (m1, _)), None ->
      begin match m1 with
        | Term.Fun ((f,_),_,[_;_;_]) -> Some m1, None
        | _ -> None, Some m1
      end
    | None, None -> None, None
    | None, Some _ -> assert false
  in

  match target with
  | Some (Term.Fun ((fnenc,indices), _, [m; Term.Name r; k]) as enc) ->
    apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k
  | Some _ ->
    soft_failure
      (Tactics.Failure ("Target must be of the form enc(_,r,_) where \
                         r is a name"))
  | None ->
    let encs =
      Iter.get_ftypes ~excludesymtype:Symbols.ADec table Symbols.AEnc e @
      Iter.get_ftypes ~excludesymtype:Symbols.SDec table Symbols.SEnc e
    in
    (** Run [apply] on first item in [encs] that is well-formed
      * and has a diff in its key.
      * We could also backtrack in case of failure. *)
    let diff_key = function
      | Term.Diff _ | Term.Fun (_, _, [Term.Diff _]) -> true
      | _ -> false
    in

    let rec find = function
      | occ :: occs ->
        if not (Sv.is_empty occ.Iter.occ_vars) then find occs
        else
        begin match occ.Iter.occ_cnt with
          | Term.Fun ((fnenc,indices), _, [m; Term.Name r; k]) as enc
            when diff_key k ->
            apply ~enc ~new_key ~fnenc ~indices ~m ~r ~k

          | _ -> find occs
        end

      | [] ->
        soft_failure
          (Tactics.Failure ("no subterm of the form enc(_,r,k) where \
                             r is a name and k contains a diff(_,_)"))
    in find encs

let () =
  T.register_typed "enckp"
    ~general_help:"Change the key in some encryption subterm."
    ~detailed_help:"This captures the fact that an encryption key may hide the \
                    key.  The term and new key can be passed as arguments, \
                    otherwise the tactic applies to the first subterm of the form \
                    enc(_,r,k) where r is a name and k features a diff operator."
    ~tactic_group:Cryptographic
    (LowTactics.genfun_of_efun_arg enckp)
    Args.(Pair (Int, Pair (Opt Message,Opt Message)))

(*------------------------------------------------------------------*)
(** XOR *)

exception Not_xor

(* Removes the first occurence of Name (n,is) in the list l. *)
let rec remove_name_occ ns l = match l with
  | [Term.Name ns'; t] when ns = ns' -> t
  | [t; Term.Name ns'] when ns = ns' -> t
  | _ ->
    Tactics.(soft_failure (Failure "name is not XORed on both sides"))

let mk_xor_phi_base (cntxt : Constr.trace_cntxt) env biframe
    (n_left, l_left, n_right, l_right, term) =
  let biframe = Term.mk_diff l_left l_right :: biframe in

  let system_left = SystemExpr.(project PLeft cntxt.system) in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = mk_phi_proj cntxt_left env n_left PLeft biframe in

  let system_right = SystemExpr.(project PRight cntxt.system) in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = mk_phi_proj cntxt_right env n_right PRight biframe in

  let len_left =
    Term.(mk_atom `Eq (mk_len l_left) (mk_len (mk_name n_left)))
  in

  let len_right =
    Term.(mk_atom `Eq (mk_len l_right) (mk_len (mk_name n_right)))
  in

  let len = if len_left = len_right then [len_left] else [len_left;len_right] in

  let phi =
    Term.mk_ands
      (* remove duplicates, and then concatenate *)
      (len @
       List.filter (fun x -> not (List.mem x phi_right)) phi_left @
       phi_right)
  in
  phi

let is_xored_diff t =
  match Term.pi_term PLeft t, Term.pi_term PRight t with
  | (Fun (fl,_,ll),Fun (fr,_,lr))
    when (fl = Term.f_xor && fr = Term.f_xor) -> true
  | _ -> false

let is_name_diff mess_name =
  match Term.pi_term PLeft mess_name, Term.pi_term PRight mess_name with
  | Name nl, Name nr -> true
  | _ -> false

let xor Args.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2)))) s =
  (* We allow the optional arguments to be in any order, we just match them
     however we can. *)
  let opt_m, opt_n =  match m1, m2 with
    | None, None -> None, None
    | Some Message (t, _), None
    | None, Some Message (t, _)
      when is_name_diff t -> None, Some t
    | Some Message (t, _), None
    | None, Some Message (t, _)
      when is_xored_diff t -> Some t, None
    | Some Message (t1, _), Some Message (t2, _)
      when is_name_diff t1 && is_xored_diff t2 -> Some t2, Some t1
    | Some Message (t1, _), Some Message (t2, _)
      when is_name_diff t2 && is_xored_diff t1 -> Some t1, Some t2
    | _ ->       soft_failure
        (Tactics.Failure
           "The optional arguments of xor can only be a name and/or the target \
            xored term.")
  in
  let before, e, after = split_equiv_goal i s in

  (* the biframe to consider when checking the freshness *)
  let biframe = List.rev_append before after in
  let cntxt = ES.mk_trace_cntxt s in
  let env = ES.env s in

  let xor_occ =
    match (Iter.get_fsymb ~allow_diff:true (ES.table s) Term.f_xor e), opt_m with
    | [], _ ->
      soft_failure
        (Tactics.Failure
           "Xor can only be applied on a term with at least one occurrence \
            of a term xor(t,k)")

    | occ :: _, None ->
      if not (Sv.is_empty occ.Iter.occ_vars) then
        soft_failure
          (Tactics.Failure "application below a binder is not supported");
      occ

    | occs, Some xor ->
      begin match
        List.find (fun xor_occ -> xor_occ.Iter.occ_cnt = xor) occs
      with
        | occ -> occ
        | exception Not_found ->
          soft_failure
            (Tactics.Failure "the given xor does not occur in the term")
      end
  in
  let t =  xor_occ.Iter.occ_cnt in

  let n_left, l_left, n_right, l_right, term =
    match opt_n with
    | None ->
      begin
        match Term.pi_term PLeft t, Term.pi_term PRight t with
        | (Fun (fl, _, [Term.Name nl;ll]),
           Fun (fr, _, [Term.Name nr;lr]))
          when (fl = Term.f_xor && fr = Term.f_xor) ->
          (nl,ll,nr,lr,t)

        | _ -> assert false
      end
    | Some mess_name ->
      begin
        match Term.pi_term PLeft mess_name, Term.pi_term PRight mess_name with
        | Name nl, Name nr ->
          begin match Term.pi_term PLeft t, Term.pi_term PRight t with
            | (Fun (fl,_,ll),Fun (fr,_,lr))
              when (fl = Term.f_xor && fr = Term.f_xor) ->
              (nl,remove_name_occ nl ll,
               nr,remove_name_occ nr lr,
               t)
            | _ -> assert false
          end
        | _ -> assert false
      end
  in
  let phi =
    mk_xor_phi_base cntxt env biframe (n_left, l_left, n_right, l_right, term)
  in
  let ndef = Symbols.{ n_iarr = 0; n_ty = Message ; } in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_XOR") ndef
  in
  let ns = Term.mk_isymb n Message [] in
  let s = ES.set_table table s in

  let then_branch = Term.mk_name ns in
  let else_branch = term in
  let if_term = Term.mk_ite phi then_branch else_branch in

  let new_elem =
    Equiv.subst_equiv [Term.ESubst (t,if_term)] [e]
  in
  let biframe = List.rev_append before (new_elem @ after) in
  [ES.set_equiv_goal biframe s]


let () =
  T.register_typed "xor"
   ~general_help:"Removes biterm (n(i0,...,ik) XOR t) if n(i0,...,ik) is fresh."
   ~detailed_help:"This yields the same freshness condition on the name as the \
                   fresh tactic."
   ~tactic_group:Cryptographic
   (LowTactics.genfun_of_pure_efun_arg xor)
   Args.(Pair (Int, Pair (Opt Message, Opt Message)))


(*------------------------------------------------------------------*)
exception Not_context

class ddh_context ~(cntxt:Constr.trace_cntxt) ~gen ~exp exact a b c
  = object (self)

 inherit Iter.iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | _ -> super#visit_macro ms a

  (* we check if the only diff are over g^ab and g^c, and that a, b and c
     appears only as g^a, g^b and g^c. *)
  method visit_message t =
    match t with
    (* any name n can occur as g^n *)
    | Term.Fun (f, _, [g1; Name n]) when f = exp && g1 = gen -> ()

    (* any names a b can occur as g^a^b *)
    | Term.(Diff(Term.(Fun (f1,_, [(Fun (f2,_, [g1; Name n1]));
                                   Name n2])),
                 Term.Fun (f, _, [g3; Name n3])))
      when f1 = exp && f2 = exp && g1 = gen && g3 = gen && n3.s_symb = c &&
           ((n1.s_symb = a && n2.s_symb = b) ||
            (n1.s_symb = b && n2.s_symb = a)) -> ()

    (* if a name a, b, c appear anywhere else, fail *)
    | Term.Name n when List.mem n.s_symb [a; b; c] -> raise Not_context

    (* if a diff is not over a valid ddh diff, we fail  *)
    | Term.Diff _ -> raise Not_context

    | _ -> super#visit_message t

end

exception Macro_found

class find_macros ~(cntxt:Constr.trace_cntxt) exact = object (self)
 inherit Iter.iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) ->
      raise Macro_found
    | _ -> self#visit_macro ms a
end


(** If all the terms of a system can be seen as a context of the terms, where
   all the names appearing inside the terms are only used inside those, returns
   true. *)
let is_ddh_context (cntxt : Constr.trace_cntxt) ~gen ~exp a b c elem_list =
  let a,b,c = Symbols.Name.of_lsymb a cntxt.table,
              Symbols.Name.of_lsymb b cntxt.table,
              Symbols.Name.of_lsymb c cntxt.table in
  let iter = new ddh_context ~cntxt ~gen ~exp false a b c in
  let iterfm = new find_macros ~cntxt false in
  let exists_macro =
    try List.iter iterfm#visit_message elem_list; false
    with Macro_found -> true
  in

  try
    (* we check that a b and c only occur in the correct form inside the system,
       if the elements contain some macro based on the system.*)
   if exists_macro then
    SystemExpr.iter_descrs cntxt.table cntxt.system (
      fun d ->
        iter#visit_message (snd d.condition) ;
        iter#visit_message (snd d.output) ;
        List.iter (fun (_,t) -> iter#visit_message t) d.updates;
    );
   (* we then check inside the frame *)
    List.iter iter#visit_message elem_list;
    true
  with Not_context | Fresh.Name_found -> false

let is_ddh_gen tbl gen =
  match Symbols.Function.get_def gen tbl with
  | _, Symbols.DDHgen -> true
  | _ -> false

let ddh (lgen : lsymb) (na : lsymb) (nb : lsymb) (nc : lsymb) s sk fk =
  let tbl = ES.table s in
  let gen_symb = Symbols.Function.of_lsymb lgen tbl in

  if not (is_ddh_gen tbl gen_symb) then
    soft_failure ~loc:(L.loc lgen)
      (Failure "no DDH assumption on this generator");

  let exp_symb = match Symbols.Function.get_data gen_symb tbl with
    | Symbols.AssociatedFunctions [exp] -> exp
    | _ -> assert false
  in

  let gen = Term.mk_fun tbl gen_symb [] [] in
  let exp = (exp_symb, []) in

  let cntxt = ES.mk_trace_cntxt s in
  if is_ddh_context ~gen ~exp cntxt na nb nc (ES.goal_as_equiv s)
  then sk [] fk
  else soft_failure Tactics.NotDDHContext

(* DDH is called on strings that correspond to names, put potentially without
   the correct arity. E.g, with name a(i), we need to write ddh a, .... Thus, we
   cannot use the typed registering, as a is parsed as a name identifier, which
   then does not have the correct arity. *)

let () = T.register_general "ddh"
    ~tactic_help:
      {general_help = "Closes the current system, if it is an \
                       instance of a context of ddh.";
       detailed_help = "It must be called on (generator, a, b, c) where \
                        (a,b,c) are strings that corresponds \
                        to names, but without any indices. It then \
                        applies ddh to all the copies of the names, \
                        and checks that all actions of the protocol \
                        uses the names in a correct way. Can be used \
                        in collaboration with some transitivity to \
                        obtain a system where ddh can be applied.";
                  usages_sorts = [Sort (Pair (String, Pair (String, Pair( String, String))))];
                  tactic_group = Cryptographic}
    (function
       | [Args.String_name gen;
          Args.String_name v1;
          Args.String_name v2;
          Args.String_name v3] ->
         LowTactics.gentac_of_etac (ddh gen v1 v2 v3)
       | _ -> bad_args ())
