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
module Args = HighTacticsArgs
module L    = Location
module SE   = SystemExpr

module ES   = EquivSequent
module Hyps = ES.Hyps

module NO = NameOccs

module LT = LowTactics
  
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

let split_equiv_goal = LT.split_equiv_goal

(*------------------------------------------------------------------*)
let wrap_fail = EquivLT.wrap_fail

let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let mk_pair_trace_cntxt (s : ES.t) : Constr.trace_cntxt =
  let se = (Utils.oget ((ES.env s).system.pair) :> SE.fset) in
  ES.mk_trace_cntxt ~se s 

let check_goal_is_equiv (s : ES.t) : unit =
  if not (Equiv.is_equiv (ES.goal s)) then
    Tactics.soft_failure (Tactics.GoalBadShape "expected an equivalence")

(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Build the sequent showing that a timestamp happens. *)
let[@warning "-32"] happens_premise (s : ES.t) (a : Term.term) =
  let s = ES.(to_trace_sequent (set_reach_goal (Term.mk_happens a) s)) in
  Goal.Trace s

(*------------------------------------------------------------------*)
let check_no_macro_or_var t =
  let exception Failed in

  let rec check t =
    match t with
    | Term.Var _ | Term.Macro _ -> raise Failed
    | _ -> Term.titer check t
  in
  try check t; true with Failed -> false

(** Closes the goal if it is an equivalence
  * where the two frames are identical. *)
let refl (e : Equiv.equiv) (s : ES.t) =
  let refl_system =
    let pair = Utils.oget ((ES.env s).system.pair) in
    snd (SE.fst pair) = snd (SE.snd pair)
  in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  (* TODO do we really need to check for variables?
     They could be an issue since they can currently
     be instantiated by terms containing diff operators. *)
  if not refl_system && not (List.for_all check_no_macro_or_var e)
  then `NoReflMacroVar
  else if ES.get_frame l_proj s = ES.get_frame r_proj s
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
    ~pq_sound:true
    (LT.genfun_of_efun refl_tac)

(*------------------------------------------------------------------*)
let sym_tac (s : ES.t) : Goal.t list =
  check_goal_is_equiv s;

  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let equiv_left = ES.get_frame l_proj s |> Utils.oget in
  let equiv_right = ES.get_frame r_proj s |> Utils.oget in
  let old_context = (ES.env s).system in
  let old_pair = Utils.oget old_context.pair in
  let new_pair =
    SE.make_pair (snd (SE.snd old_pair)) (snd (SE.fst old_pair)) in
  let new_context = { old_context with pair = Some new_pair } in
  let diff l r = Term.combine [l_proj,l; r_proj,r] in
  [ Goal.Equiv
      (ES.set_goal_in_context
         new_context
         (Atom (Equiv (List.map2 diff equiv_right equiv_left)))
         s) ]

let () =
  let tactic_help = Prover.{
      general_help = "Prove an equivalence by symmetry.";
      detailed_help =
        "Turn a goal whose conclusion is an equivalence \
         into a subgoal whose conclusion is the symmetric equivalence.\
         \n\n\
         As a side effect the system annotation must be changed, \
         which might cause the dropping of some hypotheses.";
      usages_sorts = [Sort None];
      tactic_group = Logical }
  in
  T.register "sym" ~tactic_help ~pq_sound:true
    (LT.genfun_of_efun sym_tac)

(*------------------------------------------------------------------*)

(** Prove a sequent s whose conclusion is an equivalence
    from s1,s2,s3 where:

     - s1 shows that the left projections of the equivalence
       are equivalent for the old and new left systems;

     - s3 shows that the right projections of the equivalence
       are equivalent for the old and new right systems;

     - s2 proves the same equivalence as s1 but for the new systems.

    For convenience a new context is passed and not just a new pair.
    This allows to change the set annotations for s2 by the way. *)
let transitivity_systems new_context s =
  check_goal_is_equiv s;

  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  (* Extract data from initial sequent. *)
  let equiv_left = ES.get_frame l_proj s |> Utils.oget in
  let equiv_right = ES.get_frame r_proj s |> Utils.oget in
  let old_context = (ES.env s).system in
  let old_pair = Utils.oget old_context.pair in

  let new_pair = Utils.oget new_context.SE.pair in

  (* Extract data from new context. *)
  let _, new_left = SE.fst new_pair in
  let _, new_right = SE.snd new_pair in

  (* Create new system annotations for s1 and s3.
     The order of single systems in {left,right}_systems does not
     matter for soundness but the choice below seems most natural
     to understand the chain of transitivities, and it also maximizes
     the chances that the context does not change in new sequents,
     which will allow set_goal_in_context to keep a maximum of hypotheses. *)
  let left_systems = SE.make_pair (snd (SE.fst old_pair)) new_left in
  let right_systems = SE.make_pair new_right (snd (SE.snd old_pair)) in

  let s1 =
    ES.set_goal_in_context
      { old_context with pair = Some left_systems }
      (Atom (Equiv equiv_left))
      s
  in
  let s3 =
    ES.set_goal_in_context
      { old_context with pair = Some right_systems }
      (Atom (Equiv equiv_right))
      s
  in
  let s2 = ES.set_goal_in_context new_context (ES.goal s) s in

  [Goal.Equiv s1;Goal.Equiv s2;Goal.Equiv s3]

let () =

  let tactic_help = Prover.{
    general_help = "Prove an equivalence by transitivity.";
    detailed_help =
      "When trying to prove an equivalence with respect to an initial \
       pair of systems, the tactic `trans [new_annotation]` will reduce \
       the goal to three new subgoals. Each subgoal will have as conclusion \
       an equivalence, and by transitivity the three equivalences imply \
       the initial equivalence. \
       The second subgoal will establish an equivalence that is syntactically \
       identical to the initial one, but understood with respect to \
       the new system annotation.\
       \n\n\
       The three subgoals will in general have different system annotations \
       than the initial goal. This change might force the dropping \
       of some hypotheses. Other than that, hypotheses are unchanged.";
    usages_sorts = [];
    tactic_group = Logical }
  in

  T.register_general "trans"
    ~tactic_help ~pq_sound:true
    (LT.genfun_of_efun_arg
       (fun args s -> match args with
          | [TacticsArgs.SystemAnnot annot] ->
              let context = annot (ES.env s).table in
                fun sk fk ->
                  begin match transitivity_systems context s with
                    | l -> sk l fk
                    | exception Tactics.Tactic_soft_failure e -> fk e
                  end
          | _ -> Tactics.(hard_failure (Failure "invalid arguments"))))

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : ES.t list =
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s ->
    let id, _ = Hyps.by_name str s in
    List.map
      (fun (EquivLT.CHyp _, ss) -> ss)
      (EquivLT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match EquivLT.convert_args s args Args.(Sort Term) with
    | Args.Arg (Term (ty, f, _)) ->
      begin
        match ty with
        | Type.Timestamp -> EquivLT.timestamp_case f s
        | _ -> bad_args ()
      end
    | _ -> bad_args ()


let case_tac (args : Args.parser_args) : LT.etac =
  wrap_fail (do_case_tac args)

(*------------------------------------------------------------------*)
(** For each element of the biframe, checks that it is a member of the
  * hypothesis biframe. If so, close the goal.
    If [hyp = Some id], only checks for hypothesis [id].  *)
let assumption ?hyp s =
  let goal = ES.goal s in

  let in_atom =
    (* For equivalence goals, we look for inclusion of the goal in
       an existing equivalence hypothesis *)
    if ES.goal_is_equiv s then
      let goal = ES.goal_as_equiv s in
      (function
        | Equiv.Equiv equiv  ->
          List.for_all (fun elem ->
              List.exists (ES.Reduce.conv_term s elem)
                equiv
            ) goal
        | Equiv.Reach _ -> false)

    else (fun at -> ES.Reduce.conv_equiv s (Equiv.Atom at) goal)
  in

  let in_hyp id f = 
    (hyp = None || hyp = Some id) &&
    match f with
    | Equiv.Atom at -> in_atom at
    | _ as f -> ES.Reduce.conv_equiv s f goal
  in

  if Hyps.exists in_hyp s
  then []
  else Tactics.soft_failure Tactics.NotHypothesis

let do_assumption_tac args s : ES.t list =
  let hyp =
    match Args.convert_as_lsymb args with
    | Some str -> Some (fst (Hyps.by_name str s))
    | None -> None 
  in
  assumption ?hyp s

let assumption_tac args = wrap_fail (do_assumption_tac args)

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
    (LT.genfun_of_efun byequiv_tac)


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
let simpl_ident : LT.f_simpl = fun ~red_param ~strong ~close s sk fk ->
  if close then fk (None, GoalNotClosed) else sk [s] fk

(*------------------------------------------------------------------*)
(** [generalize ts s] reverts all hypotheses that talk about [ts] in [s],
    by introducing them in the goal.
    Also returns a function that introduces back the generalized hypothesis.*)
let generalize (ts : Term.term) s =
  let ts = match ts with
    | Var t -> t
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
    match LT.do_intros_ip simpl_ident ips (Goal.Equiv s) with
    | [Goal.Equiv s] -> s
    | _ -> assert false
  in

  intro_back, s


(*------------------------------------------------------------------*)
(** Given a judgement [s] of the form Γ ⊢ E, and a timestamp τ,
    produce the judgments
    [Γ ⊢ E{ts → init}] and [(Γ, E{ts → pred τ}) ⊢ E].
    The second one is then direclty simplified by a case on all possible
    values of τ, producing a judgement for each one.
    Generalizes Γ ⊢ E over τ if necessary. *)
let induction Args.(Message (ts,_)) s =
  let env = ES.vars s in
  match ts with
  | Var t as ts ->
    (* Generalizes over [ts]. *)
    let intro_back, s = generalize ts s in

    (* Remove ts from the sequent, as it will become unused. *)
    let s = ES.set_vars (Vars.rm_var t env) s in
    let table  = ES.table s in
    let system =
      match SE.get_compatible_expr (ES.env s).system with
        | Some expr -> expr
        | None -> soft_failure (Failure "underspecified system")
    in
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

    (* Creates the goal corresponding to the case
       where [t] is instantiated by [action]. *)
    let case_of_action (action,symbol,indices) =
      let env = ref @@ ES.vars induc_s in
      let subst =
        List.map
          (fun i ->
             let i' = Vars.make_approx_r env i in
             Term.ESubst (Term.mk_var i, Term.mk_var i'))
          indices
      in
      let name =
        SE.action_to_term table system
          (Action.subst_action subst action)
      in
      let ts_subst = [Term.ESubst(ts,name)] in
      ES.subst ts_subst induc_s |> ES.set_vars !env
    in
    let case_of_action (action,symbol,indices) =
      if symbol = Symbols.init_action then None else
        Some (case_of_action (action,symbol,indices))
    in

    let goals =
      List.filter_map case_of_action (SE.actions table system) in

    List.map simpl_impl (init_s :: goals)

  | _  ->
    soft_failure
      (Tactics.Failure "expected a timestamp variable")

(*------------------------------------------------------------------*)
(** Induction *)

let old_or_new_induction args : etac =
  if Config.new_ind () then
    (EquivLT.induction_tac ~dependent:false) args
  else
    (fun s sk fk ->
       match EquivLT.convert_args s args (Args.Sort Args.Timestamp) with
       | Args.Arg (Args.Message (ts,ty)) ->
         let ss = induction (Args.Message (ts,ty)) s in
         sk ss fk
       | _ -> hard_failure (Failure "ill-formed arguments")
    )

(*------------------------------------------------------------------*)
let enrich ty f l (s : ES.t) =
  ES.set_equiv_goal (f :: ES.goal_as_equiv s) s

let enrich_a arg s =
  match 
    Args.convert_args (ES.env s) [arg] Args.(Sort Term) (Global (ES.goal s)) 
  with
  | Args.Arg (Term (ty, t, l)) -> enrich ty t l s
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
    ~pq_sound:true
    (LT.gentac_of_etac_arg enrich_tac)


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

(*------------------------------------------------------------------*)
(** Function application *)

(** Select a frame element matching a pattern. *)
let fa_select_felems (pat : Term.term Term.pat) (s : ES.t) : int option =
  let option = { Match.default_match_option with allow_capture = true; } in
  let system = match (ES.system s).pair with
    | None -> soft_failure (Failure "underspecified system")
    | Some p -> SE.reachability_context p
  in
  List.find_mapi (fun i e ->
      match Match.T.try_match ~option (ES.table s) system e pat with
      | NoMatch _ | FreeTyv -> None
      | Match _             -> Some i
    ) (ES.goal_as_equiv s)


exception No_FA of [`HeadDiff | `HeadNoFun]

let fa_expand (t:Term.t) =
  let l = match Term.head_normal_biterm t with
    | Fun (f,_,l) -> l
    | Diff _      -> raise (No_FA `HeadDiff)
    | _           -> raise (No_FA `HeadNoFun)
  in
  (* Remove of_bool(b) coming from expansion of frame macro. *)
  List.map
    (function
       | Term.Fun (f,_,[c]) when f = Term.f_of_bool -> c
       | x -> x)
    l

(** Applies Function Application on a given frame element *)
let do_fa_felem (i : int L.located) (s : ES.t) : ES.t =
  let before, e, after = split_equiv_goal i s in
  (* Special case for try find, otherwise we use fa_expand *)
  match e with
  | Find (vars,c,t,e) ->
    let env = ref (ES.vars s) in
    let vars' = List.map (Vars.make_approx_r env) vars in
    let subst =
      List.map2
        (fun i i' -> Term.ESubst (Term.mk_var i, Term.mk_var i'))
        vars vars'
    in
    let c' = Term.mk_seq0 vars c in
    let t' = Term.subst subst t in
    let biframe =
      List.rev_append before
        ([ c' ; t' ; e ] @ after)
    in
    ES.set_vars !env (ES.set_equiv_goal biframe s) 

  | Seq(vars,t) ->
    let terms = fa_expand t in
    let biframe =
      List.rev_append
        before
        ((List.map (fun t' -> Term.mk_seq0 ~simpl:true vars t') terms) @ after)
    in
    ES.set_equiv_goal biframe s 

  | _ ->
    let biframe = List.rev_append before (fa_expand e @ after) in
    ES.set_equiv_goal biframe s 

(** [do_fa_felem] with user-level errors *)
let fa_felem (i : int L.located) (s : ES.t) : ES.t list =
  try [do_fa_felem i s] with
  | No_FA `HeadDiff ->
    soft_failure ~loc:(L.loc i) (Tactics.Failure "No common construct")
  | No_FA `HeadNoFun ->
    soft_failure ~loc:(L.loc i) (Tactics.Failure "FA not applicable")

let do_fa_tac (args : Args.fa_arg list) (s : ES.t) : ES.t list =
  let args =
    let env =
      let env = ES.env s in
      let pair = Utils.oget env.system.pair in
      Env.set_system env
        SE.{ set = (pair:>SE.arbitrary) ; pair = None }
    in
    let cntxt = Theory.{ env; cntxt = InGoal; } in
    List.map (fun (mult, tpat) ->
        let t, ty = Theory.convert ~pat:true cntxt tpat in
        let pat_vars =
          Vars.Sv.filter (fun v -> Vars.is_pat v) (Term.fv t)
        in
        let pat = Term.{
            pat_tyvars = [];
            pat_vars;
            pat_term = t; }
        in
        (mult, L.loc tpat, pat)
      ) args 
  in

  let rec do1 
      (s : ES.t) 
      ((mult, loc, pat) : Args.rw_count * L.t * Term.term Term.pat)
    : ES.t 
    =
    match fa_select_felems pat s with
    | None -> 
      if mult = `Any 
      then s
      else soft_failure ~loc (Failure "FA not applicable")
    | Some i ->
      (* useless loc, as we know [i] is in range *)
      let i = L.mk_loc L._dummy i in

      let s =
        try do_fa_felem i s with
        | No_FA _ ->
          soft_failure ~loc (Failure "bad FA pattern")
      in
      match mult with
      | `Once -> s
      | `Any | `Many -> do1 s (`Any, loc, pat)
  in
  [List.fold_left do1 s args]

let fa_tac args = match args with
  | [Args.Int_parsed i] -> wrap_fail (fa_felem i)
  | [Args.Fa args] -> wrap_fail (do_fa_tac args)
  | _ -> bad_args ()


(*------------------------------------------------------------------*)
(** This function goes over all elements inside elems.  All elements that can be
   seen as duplicates, or context of duplicates, are removed. All elements that
   can be seen as context of duplicates and assumptions are removed, but
   replaced by the assumptions that appear as there subterms. *)
let filter_fa_dup (s : ES.t) assump (elems : Equiv.equiv) =
  let table = ES.table s in

  let rec doit res (elems : Equiv.equiv) =
    let rec is_fa_dup acc elems e =
      (* if an element is a duplicate wrt. elems, we remove it directly *)
      if Action.is_dup ~eq:(ES.Reduce.conv_term s) table e elems then
        (true,[])
        (* if an element is an assumption, we succeed, but do not remove it *)
      else if List.mem_cmp ~eq:(ES.Reduce.conv_term s) e assump then
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
        with No_FA _ -> (false,[])
    in
    match elems with
    | [] -> res
    | e :: els ->
      let (fa_succ,fa_rem) =  is_fa_dup [] (res@els) e in
      if fa_succ then doit (fa_rem@res) els
      else doit (e::res) els
  in
  doit [] elems

(** This tactic filters the biframe through [filter_fa_dup], passing the set of
   hypotheses to it.  This is applied automatically, and essentially leaves only
   assumptions, or elements that contain a subterm which is neither a duplicate
   nor an assumption. *)
let fa_dup (s : ES.t) : ES.t list =
  (* TODO: allow to choose the hypothesis through its id *)
  let hyp = Hyps.find_map (fun _id hyp -> match hyp with
      | Equiv.(Atom (Equiv e)) -> Some e
      | _ -> None) s in

  let hyp = Utils.odflt [] hyp in

  let biframe = ES.goal_as_equiv s
                |> List.rev
                |> filter_fa_dup s hyp
  in
  [ES.set_equiv_goal biframe s]

exception Not_FADUP_formula
exception Not_FADUP_iter

class check_fadup ~(cntxt:Constr.trace_cntxt) tau = object (self)

  inherit [Term.term list] Iter.deprecated_fold ~cntxt as super

  method check_formula f = ignore (self#fold_message [Term.mk_pred tau] f)
 
  method extract_ts_atoms phi =
    List.partition (fun t ->
        match Term.form_to_xatom t with
        | Some at when Term.ty_xatom at = Type.Timestamp -> true
        | _ -> false
      ) (Term.decompose_ands phi)

  method add_atoms atoms timestamps =
    List.fold_left (fun acc at -> 
        match Term.form_to_xatom at with
        | Some (`Comp (`Leq,tau_1,tau_2)) ->
          if List.mem tau_2 acc
          then tau_1 :: acc
          else acc
        | Some (`Comp (`Lt,tau_1,tau_2)) ->
          if (List.mem (Term.mk_pred tau_2) acc || List.mem tau_2 acc)
          then tau_1 :: acc
          else acc
        | _ -> raise Not_FADUP_iter)
      timestamps
      atoms

  method fold_message timestamps t = match t with
    | Macro (ms,[],a)
      when (ms = Term.in_macro && (a = tau || List.mem a timestamps)) ||
           (ms = Term.out_macro && List.mem a timestamps) ->
      timestamps

    | Fun (f,_, [Macro (ms,[],a);then_branch; else_branch])
      when f = Term.f_ite && ms = Term.exec_macro && List.mem a timestamps
           && Term.Smart.is_zero else_branch ->
      self#fold_message timestamps then_branch
    (* Remark: the condition that the else_branch is zero is for the
       post-quantum condition.
       It could probably be removed if
       needed, cf the issue of the CS rule in the PQ paper.*)
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

    | Fun (f, _, [t1;_]) when
        (f = Term.f_lt || f = Term.f_leq || f = Term.f_geq || f = Term.f_gt)
        && (Term.ty t1 = Type.Index || Term.ty t1 = Type.Timestamp) ->
      timestamps

    | Fun _ | Seq _ | Find _
    | ForAll _ | Exists _ -> super#fold_message timestamps t

    | Action _
    | Macro _ | Name _ | Var _ | Diff _ -> raise Not_FADUP_iter
end

let fa_dup_int (i : int L.located) s =
  let before, e, after = split_equiv_goal i s in

  let biframe_without_e = List.rev_append before after in
  let cntxt = mk_pair_trace_cntxt s in
  try
    (* we expect that e is of the form exec@pred(tau) && phi *)
    let (tau,phi) =
      let f,g = match e with
        | Term.Fun (fs,_, [f;g]) when fs = Term.f_and -> f,g

        | Term.Seq (vars, Term.Fun (fs,_, [f;g])) when fs = Term.f_and ->
          let _, subst = Term.refresh_vars `Global vars in
          Term.subst subst f,
          Term.subst subst g

        | _ -> raise Not_FADUP_formula
      in

      match f,g with
      | (Term.Macro (fm,[], Fun (fs, _, [tau])), phi) 
        when fm = Term.exec_macro && fs = Term.f_pred -> 
        (tau,phi)

      | (phi, Term.Macro (fm,[], Fun (fs, _, [tau]))) 
        when fm = Term.exec_macro && fs = Term.f_pred -> 
        (tau,phi)

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
   ~pq_sound:true
   (LT.genfun_of_pure_efun_arg fadup) Args.(Opt Int)


(*------------------------------------------------------------------*)
(** Fresh *)

let fresh_mk_direct
    (n : Term.nsymb)
    (occ : Fresh.name_occ) : Term.term
  =
  let bv, subst = Term.refresh_vars `Global occ.occ_vars in
  let cond = List.map (Term.subst subst) occ.occ_cond in

  let cond = Term.mk_ands (List.rev cond) in
  
  let j = List.map (Term.subst_var subst) occ.occ_cnt in
  Term.mk_forall ~simpl:true bv
    (Term.mk_impl cond (Term.mk_indices_neq n.s_indices j))

let fresh_mk_indirect
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (n : Term.nsymb)
    (frame_actions : Fresh.ts_occs)
    (occ : TraceTactics.fresh_occ) : Term.term
  =  
  (* for each action [a] in which [name] occurs with indices from [occ] *)
  let bv = occ.Iter.occ_vars in
  let action, occ = occ.Iter.occ_cnt in

  assert ( Sv.subset
             (Action.fv_action action)
             (Sv.union (Vars.to_set env) (Sv.of_list bv)));

  let bv, subst = Term.refresh_vars `Global bv in

  (* apply [subst] to the action and to the list of
   * indices of our name's occurrences *)
  let action =
    SE.action_to_term cntxt.table cntxt.system
      (Action.subst_action subst action)
  in

  let occ = List.map (Term.subst_var subst) occ in

  (* condition stating that [action] occurs before a macro timestamp
     occurencing in the frame *)
  let disj = Term.mk_ors (Fresh.mk_le_ts_occs action frame_actions) in

  (* condition stating that indices of name in [action] and [name] differ *)
  let form = Term.mk_indices_neq occ n.s_indices in

  Term.mk_forall ~simpl:true bv (Term.mk_impl disj form)


(** Construct the formula expressing freshness for some projection. *)
let mk_phi_proj
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    (n : Term.nsymb)
    (proj : Term.proj)
    (biframe : Term.term list) : Term.term list
  =
  let frame = List.map (Term.project1 proj) biframe in
  try
    let frame_indices : Fresh.name_occs =
      List.fold_left (fun acc t ->
          Fresh.get_name_indices_ext cntxt n.s_symb t @ acc
        ) [] frame
    in
    let frame_indices = List.sort_uniq Stdlib.compare frame_indices in

    (* direct cases (for explicit occurrences of [name] in the frame) *)
    let phi_frame = List.map (fresh_mk_direct n) frame_indices in

    let frame_actions : Fresh.ts_occs = Fresh.get_macro_actions cntxt frame in

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
    let cstate = 
      let context = 
        SE.{ set = (cntxt.system :> SE.arbitrary); pair = None; } 
      in
      Reduction.mk_cstate cntxt.table ~system:context 
    in
    List.remove_duplicate (Reduction.conv cstate) (phi_frame @ phi_actions)

  with
  | Fresh.Name_found ->
    soft_failure (Tactics.Failure "name not fresh")
  | Fresh.Var_found ->
    soft_failure
      (Failure "cannot apply fresh: the formula contains a term variable")

let fresh_cond (s : ES.t) t biframe : Term.term =
  let cntxt = mk_pair_trace_cntxt s in
  let env = ES.vars s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let n_left, n_right =
    match Term.project1 l_proj  t,
          Term.project1 r_proj t with
    | (Name nl, Name nr) -> nl, nr
    | _ -> raise Fresh.Not_name
  in

  let system_left = SE.project [l_proj] cntxt.system in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = mk_phi_proj cntxt_left env n_left l_proj biframe in

  let system_right = SE.project [r_proj] cntxt.system in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = mk_phi_proj cntxt_right env n_right r_proj biframe in

  let cstate = Reduction.mk_cstate cntxt.table in
  Term.mk_ands
    (* concatenate and remove duplicates *)
    (List.remove_duplicate (Reduction.conv cstate) (phi_left @ phi_right))


(** Returns the term [if (phi_left && phi_right) then 0 else diff(nL,nR)]. *)
let fresh_mk_if_term (s : ES.t) t biframe =
  if not Symbols.(check_bty_info (ES.table s) (Term.ty t) Ty_large) then
    soft_failure
      (Failure "name is of a type that is not [large]");

  let phi = fresh_cond s t biframe in
  Term.mk_ite phi Term.mk_zero t


let fresh i (s : ES.t) =
  let before, e, after = split_equiv_goal i s in

  (* the biframe to consider when checking the freshness *)
  let biframe = List.rev_append before after in
  (* expand the biframe to improve precision when computing the freshness
     condition *)
  let biframe_exp = 
    List.map (fun t ->
        EquivLT.expand_all_macros t (oget (ES.system s).pair :> SE.arbitrary) s
      ) biframe 
  in
  try
    let if_term = fresh_mk_if_term s e biframe_exp in
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
  match EquivLT.convert s term with
  (* we expect term to be a sequence *)
  | (Seq (vs, t) as term_seq), ty ->
    (* we parse the arguments ths, to create a substution for variables vs *)
    let subst = Theory.parse_subst (ES.env s) vs ths in

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
    ~pq_sound:true
    (LT.gentac_of_etac_arg expand_seq_tac)


(*------------------------------------------------------------------*)
(* TODO: remove this tactic *)
let ifeq Args.(Pair (Int i, Pair (Message (t1,ty1), Message (t2,ty2)))) s =

  (* check that types are equal *)
  check_ty_eq ty1 ty2;

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
    ~pq_sound:true
    (LT.genfun_of_efun_arg ifeq) Args.(Pair (Int, Pair (Message, Message)))


(*------------------------------------------------------------------*)
(** Automatic simplification *)

let goal_is_reach s =
  match ES.goal s with
  | Equiv.Atom (Reach _) -> true
  | _ -> false

let auto ~red_param ~strong ~close s sk (fk : Tactics.fk) =
  let rec auto_rec s sk fk =
    let open Tactics in
    match s with
    | Goal.Trace t ->
      let sk l fk = sk (List.map (fun s -> Goal.Trace s) l) fk in
      TraceTactics.simpl ~red_param ~close ~strong t sk fk

    | Goal.Equiv s when goal_is_reach s ->
      auto_rec (byequiv s) sk fk

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
        then sk
            [EquivLT.reduce_sequent red_param s]
            fk
        else sk [s] fk
      in

      andthen_list ~cut:true
        [try_tac reduce;
         try_tac wfadup;
         conclude]
        s sk fk
  in
  auto_rec s sk fk
    
let tac_auto ~red_param ~close ~strong args s sk (fk : Tactics.fk) =
  match args with
  | [] -> auto ~red_param ~close ~strong s sk fk
  | _ -> hard_failure (Tactics.Failure "no argument allowed")

let tac_autosimpl s = 
  tac_auto
    ~red_param:Reduction.rp_default
    ~close:false
    ~strong:false s


(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)

(*------------------------------------------------------------------*)
(** PRF axiom *)

(** From two conjunction formulas p and q, produce a minimal diff(p, q),
    of the form (p inter q) && diff (p minus q, q minus p). *)

let combine_conj_formulas (s : ES.t) p q =
  (* Turn the conjunctions into lists. *)
  let p, q = Term.decompose_ands p, Term.decompose_ands q in
  let aux_q = ref q in
  let (common, new_p) =
    List.fold_left (fun (common, r_p) p ->
        (* If an element of p is inside aux_q, remove it from aux_q and
         * add it to common, else add it to r_p. *)
        if List.exists (ES.Reduce.conv_term s p) !aux_q then
          (aux_q :=
             List.filter (fun e -> not (ES.Reduce.conv_term s e p)) !aux_q;
           (p::common, r_p))
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
       (Term.mk_diff [Term.left_proj,  Term.mk_ands new_p;
                      Term.right_proj, Term.mk_ands (List.rev !aux_q)]))


(*------------------------------------------------------------------*)
(** Application of PRF tactic on biframe element number i,
  * optionally specifying which subterm m1 should be considered. *)
let prf arg (s : ES.t) : ES.t list =
  let i, m1 =
    match arg with
    | Args.(Pair (Int i, Opt (Message, m1))) ->
      i, m1
    | _ -> assert false
  in
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let env = ES.vars s in

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
      if not (occ.Iter.occ_vars = []) then
        soft_failure
          (Tactics.Failure "application below a binder is not supported");
      occ

    | occs, Some (Message (hash, _)) ->
      match
        List.find (fun hash_occ -> hash_occ.Iter.occ_cnt = hash) occs
      with
        | occ -> occ
        | exception Not_found ->
          soft_failure
            (Tactics.Failure "the given hash does not occur in the term")
  in
  let fn, ftyp, m, key, hash = match hash_occ.Iter.occ_cnt with
    | Term.Fun ((fn,_), ftyp, [m; key]) as hash ->
      fn, ftyp, m, key, hash
    | _ -> assert false
  in

  (* The formula, without the oracle condition. *)
  let formula =
    let cntxt = mk_pair_trace_cntxt s in
    let l_proj, r_proj = ES.get_system_pair_projs s in
    let cond_l = Prf.prf_condition_side l_proj cntxt env biframe e hash in
    let cond_r = Prf.prf_condition_side r_proj cntxt env biframe e hash in

    match cond_l, cond_r with
    | None, None -> assert false

    (* the hash occurs only on one side *)
    | Some (direct, indirect), None
    | None, Some (direct, indirect) ->
      Term.mk_and ~simpl:false direct indirect

      (* the hash occurs on both side *)
    | Some (direct_l, indirect_l), Some (direct_r, indirect_r) ->
      Term.mk_and ~simpl:false
        (combine_conj_formulas s  direct_l   direct_r)
        (combine_conj_formulas s indirect_l indirect_r)
  in

  (* Check that there are no type variables. *)
  assert (ftyp.fty_vars = []);

  let nty = ftyp.fty_out in
  let ndef = Symbols.{ n_fty = Type.mk_ftype 0 [] [] nty; } in
  let table,n =
    Symbols.Name.declare (ES.table s) (L.mk_loc L._dummy "n_PRF") ndef
  in
  let ns = Term.mk_isymb n nty [] in
  let s = ES.set_table table s in

  let oracle_formula =
    Prover.get_oracle_tag_formula (Symbols.to_string fn)
  in

  let final_if_formula =
    if Term.is_false oracle_formula then
      formula
    else
      let uvarm, uvarkey, f =
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
    ~pq_sound:true
    (LT.genfun_of_pure_efun_arg prf)
    Args.(Pair(Int, Opt Message))

(*------------------------------------------------------------------*)
let global_diff_eq (s : ES.t) =
  let frame = ES.goal_as_equiv s in
  let system = Utils.oget (ES.system s).pair in
  let cntxt = mk_pair_trace_cntxt s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  (* Collect in ocs the list of diff terms that occur (directly or not)
     in [frame]. All these terms are relative to [system]. *)
  let ocs = ref [] in
  let iter x y t =
    (* rebuild a term with top-level diffs, before using 
       [simple_bi_term_no_alpha_find] to normalize it in a particular way. *)
    let t = Term.mk_diff [l_proj, Term.project1 l_proj t;
                          r_proj, Term.project1 r_proj t] in
    ocs := ( List.map (fun u -> (x,y,u))
               (Iter.get_diff ~cntxt (Term.simple_bi_term_no_alpha_find t)))
           @ !ocs 
  in
  List.iter (iter [] []) frame;

  SE.iter_descrs cntxt.table system
  (fun action_descr ->
     let miter = iter [action_descr.Action.name] action_descr.Action.indices in
     miter (snd action_descr.Action.output) ;
     miter (snd action_descr.Action.condition) ;
     List.iter (fun (_,m) -> miter m) action_descr.Action.updates) ;

  (* Function converting each occurrence to the corresponding subgoal. *)
  let subgoal_of_occ (vs,is,t) = 
    let cond = Term.mk_ands (List.rev t.Iter.occ_cond) in
    match t.Iter.occ_cnt with
    | Term.Diff (Explicit [p1,s1; p2,s2]) as subterm
      when p1 = l_proj && p2 = r_proj ->
        let fvars =
          t.Iter.occ_vars @ Vars.Sv.elements (Term.fv subterm)
        in
        let pred_ts_list =
          let iter = new Fresh.deprecated_get_actions ~cntxt in
          iter#visit_message subterm;
          iter#visit_message cond;
          iter#get_actions
        in
        (* Remark that the get_actions add pred to all timestamps, to simplify. *)
        let ts_list = 
          (List.map (fun v -> Term.mk_action v is) vs)
          @ List.map (function
              | Term.Fun (fs, _, [tau]) when fs = Term.f_pred -> tau
              | t -> t
            ) pred_ts_list 
        in

        (* free vars of [ts_list], minus [fvars] *)
        let fv_ts_list =
          let s =
            List.fold_left (fun sv ts -> 
                Sv.union sv (Term.fv ts)
              ) Sv.empty ts_list
          in
          Sv.diff s (Sv.of_list fvars)
        in

        (* add correctly the new free variables in [s] *)
        let env, _, subst = 
          Term.refresh_vars_env (ES.vars s) (Sv.elements fv_ts_list)
        in
        let ts_list = List.map (Term.subst subst) ts_list in
        let s = ES.set_vars env s in

        (* XXX the expansions that come next are inefficient (and may become
           in incorrect if we allow richer diff operators): s1 and s2 only make
           sense in projected systems, so we should not expand macros wrt s in
           them; anyway it is useless to do so if we project immediately
           afterwards. *)
        let s1 = 
          let sexpr1 = SE.project [p1] (ES.system s).set in
          Term.project1 p1
            (EquivLT.expand_all_macros ~force_happens:true s1 sexpr1 s) 
        in
        let s2 = 
          let sexpr2 = SE.project [p2] (ES.system s).set in
          Term.project1 p2
            (EquivLT.expand_all_macros ~force_happens:true s2 sexpr2 s)
        in
        Goal.Trace 
          ES.(to_trace_sequent
                (set_reach_goal
                   Term.(
                     mk_forall fvars
                       (mk_impls 
                          (List.map mk_happens ts_list
                           @ List.map (fun t -> mk_macro exec_macro [] t) ts_list
                           @ [cond])
                          (mk_atom `Eq s1 s2))
                   )
                   s))
    | _ -> assert false
  in
  List.map subgoal_of_occ !ocs

let () =
  T.register "diffeq"
        ~tactic_help:{general_help = "Closes a reflexive goal up to equalirt";
                      detailed_help = "A goal is reflexive when the left and \
                                       right frame corresponding to the bi-terms \
                                       are identical. For all diff(s1,s2), one \
                                       needs to prove that s1=s2 holds";
                  usages_sorts = [Sort None];
                  tactic_group = Structural}
    ~pq_sound:true
    (LT.genfun_of_efun global_diff_eq)


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
    Type.Lambda (List.map Vars.ty is, Type.Boolean)
  in

  let hty, ht = EquivLT.convert_ht s ht in

  check_hty_eq hty seq_hty;

  (* compute the new sequent *)
  let is, subst = Term.refresh_vars `Global is in
  let ti = Term.subst subst ti in

  let is_terms = List.map Term.mk_var is in

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

  let env = ES.vars s in
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
    (LT.gentac_of_etac_arg split_seq_tac)

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

  check_ty_eq (Term.ty t) (Term.ty seq_term);

  (* refresh the sequence *)
  let seq_vars, subst = Term.refresh_vars `Global seq_vars in
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
    (LT.genfun_of_efun_arg mem_seq_tac)

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
        let term, term_ty = EquivLT.convert s p_term in
        let p_bool_loc = L.loc p_bool in

        (* check that types are compatible *)
        let seq_hty =
          Type.Lambda (List.map Vars.ty e_is, Type.Boolean)
        in
        check_hty_eq ~loc:p_bool_loc b_ty seq_hty;

        check_ty_eq ~loc:(L.loc p_term) term_ty (Term.ty e_ti);

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
  let e_is, subst = Term.refresh_vars `Global e_is in
  let e_ti = Term.subst subst e_ti in

  (* instantiate all boolean [hterms] in [b_t_terms] using [e_is] *)
  let e_is_terms = List.map Term.mk_var e_is in
  let b_t_terms : (Term.term * Term.term) list =
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
    (LT.genfun_of_efun_arg const_seq_tac)

(*------------------------------------------------------------------*)
(** Symmetric encryption **)


(** CCA1 *)

let cca1 Args.(Int i) s =
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = mk_pair_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.vars s in

  let e = Term.head_normal_biterm e in

  let get_subst_hide_enc enc fnenc m fnpk sk fndec r eis is_top_level
    : Goal.t * Term.esubst
    =
    (* we check that the random is fresh, and the key satisfy the
       side condition. *)

    (* we create the fresh cond reachability goal *)
    let fresh_goal : Goal.t =
      let form = fresh_cond s (Term.mk_name r) biframe in
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
    if not (occ.Iter.occ_vars = []) then
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
              Euf.key_ssc ~globals:true ~elems:(ES.goal_as_equiv s)
                ~messages:[enc] ~allow_functions:(fun x -> x = fnpk)
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

  let new_elem = Equiv.subst_equiv substs [e] in
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
   ~pq_sound:true
   (LT.genfun_of_efun_arg cca1) Args.Int

(*------------------------------------------------------------------*)
(** Encryption key privacy  *)

let enckp arg (s : ES.t) =
  let i, m1, m2 =
    match arg with
    | Args.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2)))) ->
      i, m1, m2
    | _ -> assert false
  in
  let before, e, after = split_equiv_goal i s in

  let biframe = List.rev_append before after in
  let cntxt = mk_pair_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.vars s in

  (* Apply tactic to replace key(s) in [enc] using [new_key].
   * Precondition:
   * [enc = Term.Fun ((fnenc,indices), [m; Term.Name r; k])].
   * Verify that the encryption primitive is used correctly,
   * that the randomness is fresh and that the keys satisfy their SSC. *)
  let apply
      ~(enc     : Term.term)
      ~(new_key : Term.term option)
      ~(fnenc   : Term.fname)
      ~(indices : 'a)
      ~(m       : 'b)
      ~(r       : Term.nsymb)
      ~(k       : Term.term)
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
             Cca.symenc_rnd_ssc ~cntxt env fnenc sk biframe),
          (fun x -> x),
          k
        | _ -> assert false

      else
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec;fnpk] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             let errors =
               Euf.key_ssc ~globals:false
                 ~cntxt ~elems:(ES.goal_as_equiv s)
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
                (Failure
                   "The first encryption is not used \
                    with the correct public key function")
          end
        | _ -> assert false

    in
    let project = function
      | Term.Name n -> n,n
      | Term.(Diff (Explicit [_,Name l; _,Name r])) -> l,r
      | _ -> soft_failure (Failure "Secret keys must be names")
    in

    let skl, skr = project sk in
    let (new_skl, new_skr), new_key =
      match new_key with
      | Some k -> project k, k
      | None -> (skl, skl), Term.mk_name skl
    in

    check_ty_eq (Term.ty new_key) (Term.ty sk);

    (* Verify all side conditions, and create the reachability goal
     * for the freshness of [r]. *)
    let random_fresh_cond =
      try
        (* For each key we actually only need to verify the SSC
         * wrt. the appropriate projection of the system. *)
        let system = Utils.oget (ES.system s).pair in
        let l_proj, r_proj = ES.get_system_pair_projs s in
        let sysl = SE.(project [l_proj] system) in
        let sysr = SE.(project [r_proj] system) in
        List.iter (fun (ns, system) ->
            ssc (ns, (system :> SE.fset))
          )
          (List.sort_uniq Stdlib.compare
             [(skl, sysl); (skr, sysr); (new_skl, sysl); (new_skr, sysr)]) ;
        let context =
          Equiv.subst_equiv [Term.ESubst (enc,Term.empty)] [e]
        in
        fresh_cond s (Term.mk_name r) (context@biframe)
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
    (* Run [apply] on first item in [encs] that is well-formed
     * and has a diff in its key.
     * We could also backtrack in case of failure. *)
    let diff_key = function
      | Term.Diff _ | Term.Fun (_, _, [Term.Diff _]) -> true
      | _ -> false
    in

    let rec find = function
      | occ :: occs ->
        if not (occ.Iter.occ_vars = []) then find occs
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
    ~pq_sound:true
    (LT.genfun_of_efun_arg enckp)
    Args.(Pair (Int, Pair (Opt Message,Opt Message)))

(*------------------------------------------------------------------*)
(** XOR *)

(* Removes the first occurence of Name (n,is) in the list l. *)
let remove_name_occ ns l = match l with
  | [Term.Name ns'; t] when ns = ns' -> t
  | [t; Term.Name ns'] when ns = ns' -> t
  | _ ->
    Tactics.(soft_failure (Failure "name is not XORed on both sides"))

let mk_xor_phi_base (s : ES.t) biframe
    (n_left, l_left, n_right, l_right, term) =
  let cntxt = mk_pair_trace_cntxt s in
  let env = ES.vars s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let biframe =
    Term.mk_diff [l_proj,l_left;r_proj,l_right] :: biframe
  in

  let system_left = SE.project [l_proj] cntxt.system in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = mk_phi_proj cntxt_left env n_left l_proj biframe in

  let system_right = SE.project [r_proj] cntxt.system in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = mk_phi_proj cntxt_right env n_right r_proj biframe in

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

let xor arg (s : ES.t) =
  let i, m1, m2 =
    match arg with
    | Args.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2)))) -> 
      i, m1, m2
    | _ -> assert false
  in

  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let is_xored_diff t =
    match Term.project1 l_proj  t,
          Term.project1 r_proj t with
    | (Fun (fl,_,ll),Fun (fr,_,lr))
      when (fl = Term.f_xor && fr = Term.f_xor) -> true
    | _ -> false
  in
  let is_name_diff mess_name =
    match Term.project1 l_proj  mess_name,
          Term.project1 r_proj mess_name with
    | Name nl, Name nr -> true
    | _ -> false
  in
  
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
    | _ -> soft_failure
             (Tactics.Failure
                "The optional arguments of xor can only be a name and/or \
                 the target xored term.")
  in
  let before, e, after = split_equiv_goal i s in

  (* the biframe to consider when checking the freshness *)
  let biframe = List.rev_append before after in
  let xor_occ =
    match (Iter.get_fsymb ~allow_diff:true (ES.table s) Term.f_xor e), opt_m with
    | [], _ ->
      soft_failure
        (Tactics.Failure
           "Xor can only be applied on a term with at least one occurrence \
            of a term xor(t,k)")

    | occ :: _, None ->
      if not (occ.Iter.occ_vars = []) then
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
        match Term.project1 l_proj  t,
              Term.project1 r_proj t with
        | (Fun (fl, _, [Term.Name nl;ll]),
           Fun (fr, _, [Term.Name nr;lr]))
          when (fl = Term.f_xor && fr = Term.f_xor) ->
          (nl,ll,nr,lr,t)

        | _ -> soft_failure (Failure "ill-formed arguments")
      end
    | Some mess_name ->
      begin
        match Term.project1 l_proj  mess_name,
              Term.project1 r_proj mess_name with
        | Name nl, Name nr ->
          begin match Term.project1 l_proj  t,
                      Term.project1 r_proj t with
            | (Fun (fl,_,ll),Fun (fr,_,lr))
              when (fl = Term.f_xor && fr = Term.f_xor) ->
              (nl,remove_name_occ nl ll,
               nr,remove_name_occ nr lr,
               t)
            | _ -> soft_failure (Failure "ill-formed arguments")
          end
        | _ -> soft_failure (Failure "ill-formed arguments")
      end
  in
  let phi =
    mk_xor_phi_base s biframe (n_left, l_left, n_right, l_right, term)
  in
  let ndef = Symbols.{ n_fty = Type.mk_ftype 0 [] [] Message ; } in
  let table,n =
    Symbols.Name.declare (ES.table s) (L.mk_loc L._dummy "n_XOR") ndef
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
   ~pq_sound:true
   (LT.genfun_of_pure_efun_arg xor)
   Args.(Pair (Int, Pair (Opt Message, Opt Message)))


(*------------------------------------------------------------------*)
exception Not_context

class ddh_context
    ~(cntxt:Constr.trace_cntxt) ~gen ~exp ~l_proj ~r_proj exact a b c
  = object (self)

 inherit Iter.deprecated_iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | _ -> super#visit_macro ms a

  (* we check if the only diff are over g^ab and g^c, and that a, b and c
     appears only as g^a, g^b and g^c. *)
  (* if we ever decide to rewrite this tactic or generalize it,
     we may want to use functions from dh.ml written for cdh/gdh,
     that do this in a more general way *)
  method visit_message t =
    match Term.project1 l_proj t, 
          Term.project1 r_proj t with
    (* left:  a b can occur as g^a^b 
       right: c can occur as g^c *)
    | Term.(Fun (f1,_, [(Fun (f2,_, [g1; Name n1])); Name n2])),
      Term.(Fun (f, _, [g3; Name n3])) 
      when f1 = exp && f2 = exp && g1 = gen && g3 = gen && n3.s_symb = c &&
           ((n1.s_symb = a && n2.s_symb = b) ||
            (n1.s_symb = b && n2.s_symb = a)) -> ()

    | _ ->
      match t with
      (* any name n can occur as g^n *)
      | Term.Fun (f, _, [g1; Name n]) when f = exp && g1 = gen -> ()

      (* if a name a, b, c appear anywhere else, fail *)
      | Term.Name n when List.mem n.s_symb [a; b; c] -> raise Not_context

      (* if a diff is not over a valid ddh diff, we fail  *)
      | Term.Diff _ -> raise Not_context

      | _ -> super#visit_message t

end

(*------------------------------------------------------------------*)
exception Macro_found

class find_macros ~(cntxt:Constr.trace_cntxt) exact = object (self)
 inherit Iter.deprecated_iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) ->
      raise Macro_found
    | _ -> self#visit_macro ms a
end


(** If all the terms of a system can be seen as a context of the terms, where
    all the names appearing inside the terms are only used inside those, returns
    true. *)
let is_ddh_context
    ~(cntxt : Constr.trace_cntxt)
    ~l_proj ~r_proj
    ~gen ~exp a b c elem_list =
  let a,b,c = Symbols.Name.of_lsymb a cntxt.table,
              Symbols.Name.of_lsymb b cntxt.table,
              Symbols.Name.of_lsymb c cntxt.table in
  let iter = new ddh_context ~cntxt ~l_proj ~r_proj ~gen ~exp false a b c in
  let iterfm = new find_macros ~cntxt false in
  let exists_macro =
    try List.iter iterfm#visit_message elem_list; false
    with Macro_found -> true
  in

  try
    (* we check that a b and c only occur in the correct form inside the system,
       if the elements contain some macro based on the system.*)
   if exists_macro then
    SE.iter_descrs cntxt.table cntxt.system (
      fun d ->
        iter#visit_message (snd d.condition) ;
        iter#visit_message (snd d.output) ;
        List.iter (fun (_,t) -> iter#visit_message t) d.updates;
    );
   (* we then check inside the frame *)
    List.iter iter#visit_message elem_list;
    true
  with Not_context | Fresh.Name_found -> false

(*------------------------------------------------------------------*)
let is_ddh_gen tbl gen =
  match Symbols.Function.get_def gen tbl with
  | _, Symbols.DHgen l -> List.mem Symbols.DH_DDH l
  | _ -> false

(*------------------------------------------------------------------*)
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

  let cntxt = mk_pair_trace_cntxt s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  if is_ddh_context ~gen ~exp ~cntxt ~l_proj ~r_proj na nb nc (ES.goal_as_equiv s)
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
                  usages_sorts = [Sort (Pair (String, 
                                              Pair (String, 
                                                    Pair( String, String))))];
                  tactic_group = Cryptographic}
    (function
       | [Args.String_name gen;
          Args.String_name v1;
          Args.String_name v2;
          Args.String_name v3] ->
         LT.gentac_of_etac (ddh gen v1 v2 v3)
       | _ -> bad_args ())
