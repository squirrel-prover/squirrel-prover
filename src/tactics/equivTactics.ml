(** All equivalence tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Strucutral -> relies on properties of protocols, or of equality over
      messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be
      assumed.
*)
open Squirrelcore

open Utils

module T    = ProverTactics
module Args = HighTacticsArgs
module L    = Location
module SE   = SystemExpr

module TopHyps = Hyps
  
module ES   = EquivSequent
module Hyps = ES.Hyps

module NO = NameOccs
module O  = Occurrences
module Name = O.Name

module LT = LowTactics
  
module Sv = Vars.Sv
              
type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
(** {2 Utilities} *)

let split_equiv_conclusion = LT.split_equiv_conclusion

(*------------------------------------------------------------------*)
let wrap_fail = EquivLT.wrap_fail

let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let mk_pair_trace_cntxt = ES.mk_pair_trace_cntxt

let check_conclusion_is_equiv = ES.check_conclusion_is_equiv
(*------------------------------------------------------------------*)
(** {2 Logical Tactics} *)

(** Build the sequent showing that a timestamp happens. *)
let[@warning "-32"] happens_premise (s : ES.t) (a : Term.term) =
  let s = ES.(to_trace_sequent (set_reach_conclusion (Term.mk_happens a) s)) in
  Goal.Local s

(*------------------------------------------------------------------*)
let check_no_macro_or_var (env : Env.t) ~refl_system (t : Term.term) =
  let exception Failed in

  let check : Match.Pos.f_map = fun t _system fv _conds _p ->
    match t with
    | Term.Var _ -> 
      let env =
        Env.update ~vars:(Vars.add_vars (Vars.Tag.global_vars ~const:true fv) env.vars) env
      in
      if not (HighTerm.is_system_indep env t) then raise Failed;
      `Continue

    | Term.Macro _ when not refl_system -> raise Failed

    | _ -> `Continue
  in
  try
    let _, _ = Match.Pos.map check env.system.set t in
    true
  with Failed -> false

(** Closes the goal if it is an equivalence
  * where the two frames are identical. *)
let refl (e : Equiv.equiv) (s : ES.t) =
  let system_pair = Utils.oget ((ES.env s).system.pair) in
  let env_pair = Env.update ~system:{ set = (system_pair :> SE.t); pair = None; } (ES.env s) in
  let refl_system =
    snd (SE.fst system_pair) = snd (SE.snd system_pair)
  in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  if not (List.for_all (check_no_macro_or_var env_pair ~refl_system) e)
  then `NoReflMacroVar
  else
    match ES.get_frame l_proj s, ES.get_frame r_proj s with
    | Some el, Some er ->
      if List.for_all2 (ES.Reduce.conv_term ~se:(system_pair :> SE.t) s) el er
      then `True
      else `NoRefl

    | _ -> `NoRefl


(** Tactic that succeeds (with no new subgoal) on equivalences
  * where the two frames are identical. *)
let refl_tac (s : ES.t) =
  match refl (ES.conclusion_as_equiv s) s with
    | `True           -> []
    | `NoRefl         -> soft_failure (Tactics.NoRefl)
    | `NoReflMacroVar -> soft_failure (Tactics.NoReflMacroVar)

let () =
  T.register "refl"
    ~pq_sound:true
    (LT.genfun_of_efun refl_tac)

(*------------------------------------------------------------------*)
let sym_tac (s : ES.t) : Goal.t list =
  check_conclusion_is_equiv s;

  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let equiv_left = ES.get_frame l_proj s |> Utils.oget in
  let equiv_right = ES.get_frame r_proj s |> Utils.oget in
  let old_context = (ES.env s).system in
  let old_pair = Utils.oget old_context.pair in
  let new_pair =
    SE.make_pair (snd (SE.snd old_pair)) (snd (SE.fst old_pair)) in
  let new_context = { old_context with pair = Some new_pair } in
  let diff l r = Term.combine [l_proj,l; r_proj,r] in
  [ Goal.Global
      (ES.set_conclusion_in_context
         new_context
         (Atom (Equiv (List.map2 diff equiv_right equiv_left)))
         s) ]

let () =
  T.register "sym"
    ~pq_sound:true
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
  check_conclusion_is_equiv s;

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
     which will allow set_conclusion_in_context to keep a maximum of
     hypotheses. *)
  let left_systems = SE.make_pair (snd (SE.fst old_pair)) new_left in
  let right_systems = SE.make_pair new_right (snd (SE.snd old_pair)) in

  let s1 =
    ES.set_conclusion_in_context
      { old_context with pair = Some left_systems }
      (Atom (Equiv equiv_left))
      s
  in
  let s3 =
    ES.set_conclusion_in_context
      { old_context with pair = Some right_systems }
      (Atom (Equiv equiv_right))
      s
  in
  let s2 = ES.set_conclusion_in_context new_context (ES.conclusion s) s in

  [Goal.Global s1;Goal.Global s2;Goal.Global s3]

(* Term transitivity, on the right:
   u ~_{L,R} w -> 
   w ~_{R,R} v -> 
   u ~_{L,R} v *)
let trans_terms (args : (int L.located * Theory.term) list) (s : ES.t) : Goal.t list =
  let _, r_sys = SE.snd (ES.get_system_pair s) in
  let l_proj, r_proj = ES.get_system_pair_projs s in

  let cenv =
    (* fset with only the right system, once *)
    let fset_r = SE.make_fset (ES.table s) ~labels:[Some r_proj] [r_sys] in
    
    (* remove the pair when parsing, to prevent diffs *)
    let system = SE.{ set = (fset_r :> SE.arbitrary); pair = None; } in
    let env = { (ES.env s) with system; } in
    Theory.{ env; cntxt = InGoal; } 
  in

  let args = List.map (fun (i,t) -> i, fst (Theory.convert cenv t)) args in

  let equiv = ES.conclusion_as_equiv s in

  let context = ES.system s in

  let l_system, r_system = 
    let pair = Utils.oget context.pair in
    snd (SE.fst pair), snd (SE.snd pair)
  in

  let pair1 = SE.make_pair l_system r_system in (* L/R *)
  let pair2 = SE.make_pair r_system r_system in (* R/R *)

  (* fset with only the right system, twice *)
  let fset_r2 =
    SE.make_fset (ES.table s) ~labels:[Some l_proj;Some r_proj] [r_sys; r_sys]
  in
  
  let context1 = { context with pair = Some pair1; } in
  let context2 = SE.{ set = (fset_r2 :> SE.arbitrary); pair = Some pair2; } in
  
  let equiv1, equiv2 = 
    List.mapi (fun i t ->
        let t1 = Term.project1 l_proj t in
        let t2 = Term.project1 r_proj t in
        match List.find_opt (fun (j,_) -> i = L.unloc j) args with
        | None ->
          t, 
          Term.simple_bi_term
            [l_proj; r_proj]
            (Term.mk_diff [(l_proj, t2); (r_proj,    t2)])
            
        | Some (_,new_t) ->
          Term.mk_diff [(l_proj,    t1); (r_proj, new_t) ],
          Term.mk_diff [(l_proj, new_t); (r_proj,    t2) ]
      ) equiv
    |> List.split
  in
  
  let goal1 = ES.set_conclusion_in_context context1 (Atom (Equiv equiv1)) s in
  let goal2 = ES.set_conclusion_in_context context2 (Atom (Equiv equiv2)) s in


  [Goal.Global goal1; Goal.Global goal2 ]
          

let trans_tac args s =
  match args with
  | [Args.Trans (Args.TransSystem annot)] ->
    let context = SE.Parse.parse_sys (ES.table s) annot in
    fun sk fk ->
      begin match transitivity_systems context s with
        | l -> sk l fk
        | exception Tactics.Tactic_soft_failure e -> fk e
      end

  | [Args.Trans (Args.TransTerms l)] ->
    fun sk fk -> 
      begin match trans_terms l s with
        | l -> sk l fk
        | exception Tactics.Tactic_soft_failure e -> fk e
      end

  | _ -> bad_args ()

let () =
  T.register_general "trans"
    ~pq_sound:true
    (LT.genfun_of_efun_arg trans_tac)

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : ES.t list =
  let structure_based, type_based, args = match args with
    | Args.(Named_args [NArg {L.pl_desc="struct"}])::args -> true,false,args
    | Args.(Named_args [NArg {L.pl_desc="type"}])::args -> false,true,args
    | Args.Named_args [] :: args -> true,true,args
    | Args.(Named_args ((NArg s | NList (s,_))::_)) :: _ ->
      Tactics.(hard_failure ~loc:(L.loc s) (Failure "invalid argument"))
    | _ ->
      Tactics.(hard_failure (Failure "incorrect case arguments"))
  in
  match Args.convert_as_lsymb args with
  | Some str when Hyps.mem_name (L.unloc str) s && structure_based ->
    let id, _ = Hyps.by_name str s in
    List.map
      (fun (EquivLT.CHyp _, ss) -> ss)
      (EquivLT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match EquivLT.convert_args s args Args.(Sort Term) with
    | Args.Arg (Term (ty, f, loc)) ->
      begin
        match ty with
        | Type.Timestamp when type_based ->
          let env = ES.env s in
          if not (HighTerm.is_constant     env f &&
                  HighTerm.is_system_indep env f   ) then
            hard_failure ~loc
              (Failure "global case must be on a constant and \
                        system-independent term");

          EquivLT.timestamp_case f s

        | _ -> bad_args ()
      end
    | _ -> bad_args ()

let case_tac (args : Args.parser_args) : LT.etac =
  wrap_fail (do_case_tac args)

(*------------------------------------------------------------------*)
(** Apply the entailment (i.e. bi-frame inclusion) and left-false rule.
   
    Entailment is checked by verifying that there exists an hypothesis H 
    such that each element of the biframe in conclusion appears in H.

    If [hyp = Some id], only checks for hypothesis [id]. *)
let assumption ?(hyp : Ident.t option) (s : ES.t) : ES.t list =
  let conclusion = ES.conclusion s in

  let is_false = function
    | Equiv.Reach f -> ES.Reduce.conv_term s f Term.mk_false
    | _ -> false
  in

  let in_atom : Equiv.atom -> bool =
    (* For equivalence goals, we look for inclusion of the goal in
       an existing equivalence hypothesis *)
    if ES.conclusion_is_equiv s then
      let conclusion = ES.conclusion_as_equiv s in
      (function
        | Equiv.Equiv equiv  ->
          List.for_all (fun elem ->
              List.exists (ES.Reduce.conv_term s elem)
                equiv
            ) conclusion
        | Equiv.Pred  _ -> false
        | Equiv.Reach _ -> false)

    else (fun at -> ES.Reduce.conv_global s (Equiv.Atom at) conclusion)
  in

  let in_hyp (id,ldc) =
    (hyp = None || hyp = Some id) &&
    ( match ldc with
      | TopHyps.LHyp (Equiv.Atom at) -> is_false at || in_atom at
      | TopHyps.LHyp f -> ES.Reduce.conv_global s f conclusion
      | TopHyps.LDef _ -> false)
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
let byequiv s = Goal.Local (ES.to_trace_sequent s)

let byequiv_tac s = [byequiv s]

let () =
  T.register "byequiv"
    (LT.genfun_of_efun byequiv_tac)

(*------------------------------------------------------------------*)
let constraints (s : ES.t) : ES.t list =
  let s = ES.set_conclusion (Equiv.Atom (Equiv.Reach (Term.mk_false))) s in
  let trace_s = ES.to_trace_sequent s in
  List.map (fun s_t -> 
      ES.set_conclusion (Equiv.Atom (Equiv.Reach (TS.conclusion s_t))) s
    ) (TraceTactics.constraints_ttac trace_s)

let constraints_tac args : LT.etac = 
  match args with
  | [] -> wrap_fail constraints
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
(** [tautology f s] tries to prove that [f] is always true in [s]. *)
let rec tautology (f : Equiv.form) (s : ES.t) : bool =
  match f with
  | Equiv.Impl (f0,f1) ->
    let s = Hyps.add Args.AnyName (LHyp f0) s in
    tautology f1 s

  | Equiv.And (f0,f1) ->
    tautology f0 s && tautology f1 s

  | Equiv.Or (f0,f1) ->
    tautology f0 s || tautology f1 s

  | Equiv.Let _ | Equiv.Quant _ -> false

  | Equiv.(Atom (Pred _)) -> false
    
  | Equiv.(Atom (Equiv e)) -> refl e s = `True

  | Equiv.(Atom (Reach _)) ->
    let s = ES.set_conclusion f s in
    let trace_s = ES.to_trace_sequent s in
    (* TODO: improve automation by doing more than just constraint solving ? *)
    TraceTactics.constraints trace_s

(** [form_simpl_impl f s] simplifies the formula [f] in [s], by trying to
    prove [f]'s hypotheses in [s]. *)
let rec form_simpl_impl (f : Equiv.form) (s : ES.t) : Equiv.form =
  match f with
  | Equiv.Impl (f0, f1) ->
    if tautology f0 s then form_simpl_impl f1 s else f
  | _ -> f

let simpl_impl (s : ES.t) : ES.t =
  Hyps.mapi
    ~hyp:(fun id f ->
        let s_minus = Hyps.remove id s in
        form_simpl_impl f s_minus
      )
    ~def:(fun _ (se,t) -> se,t) (* leave definitions un-simplified here (for now) *)
    s


(*------------------------------------------------------------------*)
(* Simplification function doing nothing. *)
let[@warning "-27"] simpl_ident : LT.f_simpl = 
  fun ~red_param ~strong ~close s sk fk ->
  if close then fk (None, GoalNotClosed) else sk [s] fk

(*------------------------------------------------------------------*)
(** [generalize ts s] reverts all hypotheses that talk about [ts] in [s],
    by introducing them in the conclusion.
    Also returns a function that introduces back the generalized 
    hypotheses or definitions.*)
let generalize (ts : Term.term) (s : ES.t) : (ES.t -> ES.t) * ES.t =
  let ts =
    match ts with
    | Var t -> t
    | _ -> hard_failure (Failure "timestamp is not a var")
  in

  let togen =
    Hyps.fold (fun id ldc togen ->
        let fv =
          match ldc with
          | LHyp f     -> Equiv.fv f
          | LDef (_,t) -> Term.fv  t
        in
        if Sv.mem ts fv
        then id :: togen
        else togen
      ) s []
  in

  (* Generalized sequent *)
  let s = List.fold_left (fun s id -> EquivLT.revert id s) s togen in
  (* FIXME: location for [revert] *)

  (* Function introducing back generalized hypotheses or definitions *)
  let intro_back (s : ES.t) : ES.t =
    let ips = List.rev_map (fun id ->
        let ip = Args.Named (Ident.name id) in
        Args.(Simpl (SNamed ip))
      ) togen
    in
    match LT.do_intros_ip simpl_ident ips (Goal.Global s) with
    | [Goal.Global s] -> s
    | _ -> assert false
  in

  intro_back, s


(*------------------------------------------------------------------*)
(** Given a judgement [s] of the form [Γ ⊢ E], and a term [τ]
    (of type timestamp), produce the judgments

    [Γ ⊢ E{ts → init}] and [(Γ, E{ts → pred τ}) ⊢ E].

    The second judgement is then simplified by a case on [τ].
    Generalizes [Γ ⊢ E] over [τ] if necessary. *)
let old_induction Args.(Message (ts,_)) s =
  assert (Type.equal (Term.ty ts) Type.ttimestamp);

  let env = ES.env s in
  if not (HighTerm.is_constant     env ts &&
          HighTerm.is_system_indep env ts   ) then
    hard_failure 
      (Failure "simple global induction must be on a constant and \
                system-independent timestamp term (maybe try dependent induction ?)");

  let env = ES.env s in
  match ts with
  | Var t as ts ->
    (* Generalizes over [ts]. *)
    let intro_back, s = generalize ts s in

    (* Remove ts from the sequent, as it will become unused. *)
    let s = ES.set_vars (Vars.rm_var t env.vars) s in
    let table  = ES.table s in
    let system =
      match SE.get_compatible_expr (ES.env s).system with
        | Some expr -> expr
        | None -> soft_failure (Failure "underspecified system")
    in
    let subst = [Term.ESubst (ts, Term.mk_pred ts)] in
    let conclusion = ES.conclusion s in

    let ind_hyp = Equiv.subst subst conclusion in
    (* Introduce back generalized hypotheses. *)
    let induc_s = intro_back s in
    (* Introduce induction hypothesis. *)
    let _id_ind, induc_s = Hyps.add_i (Args.Named "IH") (LHyp ind_hyp) induc_s in

    let init_conclusion = Equiv.subst [Term.ESubst(ts,Term.init)] conclusion in
    let init_s = ES.set_conclusion init_conclusion s in
    let init_s = intro_back init_s in

    let const = HighTerm.is_constant env ts in
    
    (* Creates the conclusion corresponding to the case
       where [t] is instantiated by [action]. *)
    let case_of_action (action,_symbol,indices) =
      let env = ref @@ ES.vars induc_s in
      let subst =
        List.map
          (fun i ->
             let i' = Vars.make_approx_r env i (Vars.Tag.make ~const Vars.Global) in
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
        Some (case_of_action ((Action.to_action action),symbol,indices))
    in

    let conclusions =
      List.filter_map case_of_action (SE.actions table system) 
    in

    List.map simpl_impl (init_s :: conclusions)

  | _  ->
    soft_failure
      (Tactics.Failure "expected a variable of finite type")

(*------------------------------------------------------------------*)
(** Induction *)

let old_or_new_induction args : etac =
  (fun s sk fk ->
     if TConfig.new_ind (LowEquivSequent.table s) then
       (EquivLT.induction_tac ~dependent:false) args s sk fk
     else
       match EquivLT.convert_args s args (Args.Sort Args.Message) with
       | Args.Arg (Args.Message (ts,ty)) ->
         if Type.equal ty Type.ttimestamp then
           let ss = old_induction (Args.Message (ts,ty)) s in
           sk ss fk
         else
           (* use the new induction principle over types different from timestamp. *)
           EquivLT.induction_tac ~dependent:false args s sk fk
       | _ -> hard_failure (Failure "ill-formed arguments")
  )

(*------------------------------------------------------------------*)
let enrich _ty f _loc (s : ES.t) =
  ES.set_equiv_conclusion (f :: ES.conclusion_as_equiv s) s

let enrich_a arg s =
  match 
    let env = ES.env s in
    let env =
      Env.{env with
           system = SE.{set = (ES.get_system_pair s :> SE.arbitrary);
                        pair = None;} }
    in
    Args.convert_args env [arg] Args.(Sort Term) (Global (ES.conclusion s)) 
  with
  | Args.Arg (Term (ty, t, loc)) -> enrich ty t loc s
  | _ -> bad_args ()

let enrichs args s =
  List.fold_left (fun s arg -> enrich_a arg s) s args

let enrich_tac args s sk fk =
  try sk [enrichs args s] fk with
  | Tactics.Tactic_soft_failure e -> fk e

let () =
  T.register_general "enrich"
    ~pq_sound:true
    (LT.gentac_of_etac_arg enrich_tac)


(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

(*------------------------------------------------------------------*)
(** Function application *)

(** Select a frame element matching a pattern. *)
let fa_select_felems ~ty_env (pat : Term.term Term.pat_op) (s : ES.t) : int option =
  let option = { Match.default_match_option with allow_capture = true; } in
  let system = match (ES.system s).pair with
    | None -> soft_failure (Failure "underspecified system")
    | Some p -> SE.reachability_context p
  in
  List.find_mapi (fun i e ->
      match 
        Match.T.try_match ~ty_env ~option ~env:(ES.vars s) (ES.table s) system e pat 
      with
      | NoMatch _ -> None
      | Match _   -> Some i
    ) (ES.conclusion_as_equiv s)

(*------------------------------------------------------------------*)
exception No_FA of [`HeadDiff | `HeadNoFun]

let fa_expand (s : ES.t) (t : Term.t) : Term.terms =
  let env = ES.env s in
  let is_deducible_vars (l : Term.terms) : bool =
    List.for_all (fun t ->
        Term.is_var t &&
        HighTerm.is_ptime_deducible ~si:true env t
      ) l
  in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  let l =
    match Term.head_normal_biterm [l_proj; r_proj] t with
    | Tuple l ->
      if is_deducible_vars l then [] else l

    (* use [tf] to check that the function symbol is pptime computable. *)
    | Fun _ as tf -> 
      if HighTerm.is_ptime_deducible ~si:true env tf then [] else 
        raise (No_FA `HeadNoFun)

    | App (Fun _ as tf, [Tuple l]) 
    | App (Fun _ as tf, l) -> 
      let l = if is_deducible_vars l then [] else l in
      let tf = if HighTerm.is_ptime_deducible ~si:true env tf then [] else [tf] in
      tf @ l

    | Proj (_,t) -> if is_deducible_vars [t] then [] else [t]

    | App (t,l) -> if is_deducible_vars (t :: l) then [] else t :: l

    | Diff _      -> raise (No_FA `HeadDiff)
    | _           -> raise (No_FA `HeadNoFun)
  in
  (* Remove of_bool(b) coming from expansion of frame macro. *)
  List.map (function
      | Term.App (Term.Fun (f,_),[c]) when f = Term.f_of_bool -> c
      | x -> x
    ) l

(*------------------------------------------------------------------*)
let fa_check_vars_fixed_and_finite ~loc table (vs : Vars.vars) : unit =
  let bad_vars = 
    List.filter (fun v -> 
        not (Symbols.TyInfo.is_finite table (Vars.ty v) && 
             Symbols.TyInfo.is_fixed  table (Vars.ty v))
      ) vs
  in
  if bad_vars <> [] then
    soft_failure ~loc
      (Failure (Fmt.str 
                  "FA does not apply to sequences over types which are not \
                   finite and of fixed-sized: %a" Vars.pp_list bad_vars))
      
(** Applies Function Application on a given frame element *)
let do_fa_felem (i : int L.located) (s : ES.t) : ES.t =
  let before, e, after = split_equiv_conclusion i s in
  (* Special case for try find, otherwise we use fa_expand *)
  match e with
  | Find (vars,c,t,e) ->
    (* check that variables are of correct types (i.e. finite and of fixed size) *)
    fa_check_vars_fixed_and_finite ~loc:(L.loc i) (ES.table s) vars;

    let env = ref (ES.vars s) in
    let vars, subst =
      let new_vars =
        List.map (fun v -> Vars.make_approx_r env v (Vars.Tag.make ~const:true Vars.Global)) vars
      in
      let subst = 
        List.map2
          (fun i i' -> Term.ESubst (Term.mk_var i, Term.mk_var i'))
          vars new_vars
      in 
      (new_vars, subst)
    in
    let c, t = Term.subst subst c, Term.subst subst t in

    let c_seq = Term.mk_seq vars c in
    let biframe = List.rev_append before ([ c_seq ; t ; e ] @ after) in
    ES.set_vars !env (ES.set_equiv_conclusion biframe s) 

  | Quant ((Seq | Lambda),vars,t) ->
    (* this rules applies to [Seq] and [Lambda] over arbitrary types *)
    let terms = fa_expand s t in
    let biframe =
      List.rev_append
        before
        ((List.map (fun t' -> Term.mk_seq ~simpl:true vars t') terms) @ after)
    in
    ES.set_equiv_conclusion biframe s 

  | _ ->
    let biframe = List.rev_append before (fa_expand s e @ after) in
    ES.set_equiv_conclusion biframe s 

(** [do_fa_felem] with user-level errors *)
let fa_felem (i : int L.located) (s : ES.t) : ES.t list =
  try [do_fa_felem i s] with
  | No_FA `HeadDiff ->
    soft_failure ~loc:(L.loc i) (Tactics.Failure "No common construct")
  | No_FA `HeadNoFun ->
    soft_failure ~loc:(L.loc i) (Tactics.Failure "FA not applicable")

let do_fa_tac (args : Args.fa_arg list) (s : ES.t) : ES.t list =

  (* parsing context for [fa_arg] *)
  let cntxt = 
    let env =
      let env = ES.env s in
      let pair = Utils.oget env.system.pair in
      Env.set_system env
        SE.{ set = (pair:>SE.arbitrary) ; pair = None }
    in
    Theory.{ env; cntxt = InGoal; } 
  in

  (* parse one [fa_arg] *)
  let parse_fa_arg_pat
      ty_env (tpat : Theory.term)
    : L.t * Term.term Term.pat_op
    =
    let t, _ty = Theory.convert ~ty_env ~pat:true cntxt tpat in
    let vars =
      Sv.elements (Sv.filter (fun v -> Vars.is_pat v) (Term.fv t))
    in
    let pat = Term.{
        pat_op_tyvars = [];
        pat_op_vars   = Vars.Tag.local_vars vars;
        (* local inforation, since we allow to match diff operators *)

        pat_op_term   = t; }
    in
    (L.loc tpat, pat)
  in

  let rec do1 (s : ES.t) (mult, arg_pat : Args.fa_arg) : ES.t =
    (* Create a new type unification environement.
       Remark: we will never close it, as it is only used to selection a
       matching element in the bi-frame. *)
    let ty_env = Type.Infer.mk_env () in

    (* parse the function  *)
    let loc, pat = parse_fa_arg_pat ty_env arg_pat in

    if mult = Args.Exact 0 then s else
      match fa_select_felems ~ty_env pat s with
      | None -> 
        if mult = Args.Any 
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
        | Args.Once | Args.Exact 1 -> s

        | Args.Any | Args.Many -> do1 s (Args.Any, arg_pat)

        | Args.Exact i -> do1 s (Args.Exact (i - 1), arg_pat)
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
    replaced by the assumptions that appear as there subterms. 

    Used in automatic simplification with FA. *)
let filter_fa_dup (s : ES.t) (assump : Term.terms) (elems : Equiv.equiv) =
  let table = ES.table s in

  let rec is_fa_dup (elems : Term.terms) (e : Term.term) =
    (* if an element is a duplicate wrt. elems, we remove it directly *)
    if Action.is_dup ~eq:(ES.Reduce.conv_term s) table e elems then
      (true,[])
      (* if an element is an assumption, we succeed, but do not remove it *)
    else if List.mem_cmp ~eq:(ES.Reduce.conv_term s) e assump then
      (true,[e])
      (* otherwise, we go recursively inside the sub-terms produced by function
         application *)
    else try
        let new_els = fa_expand s e in
        List.fold_left
          (fun (aux1,aux2) e ->
             let (fa_succ,fa_rem) = is_fa_dup elems e in
             fa_succ && aux1, fa_rem @ aux2)
          (true,[]) new_els
      with No_FA _ -> (false,[])
  in

  let rec doit (res : Term.terms) (elems : Equiv.equiv) =
    match elems with
    | [] -> res
    | e :: els ->
      let fa_succ, fa_rem =  is_fa_dup (res @ els) e in
      if fa_succ then doit (fa_rem @ res) els
      else doit (e :: res) els
  in
  doit [] elems

(** This tactic filters the biframe through [filter_fa_dup], passing the set of
    hypotheses to it.  This is applied automatically, and essentially leaves only
    assumptions, or elements that contain a subterm which is neither a duplicate
    nor an assumption. *)
let fa_dup (s : ES.t) : ES.t list =
  (* TODO: allow to choose the hypothesis through its id *)
  let hyp =
    Hyps.find_map (fun (_, hyp) ->
        match hyp with
        | TopHyps.LHyp (Equiv.Atom (Equiv e)) -> Some e
        | _ -> None) s
  in

  let hyp = Utils.odflt [] hyp in

  let biframe =
    ES.conclusion_as_equiv s
    |> List.rev
    |> filter_fa_dup s hyp
  in
  [ES.set_equiv_conclusion biframe s]

(*------------------------------------------------------------------*)
(** Deduce. 
    FIXME : is considered pq-sound, since apply is, but this has not been checked.*)

(** Deduce recursively removed all elements of a biframe that are deducible from the other ones.*)
let deduce_all (s:ES.t) =  
    let table,system = ES.table s, ES.system s in
    let hyps = ES.get_trace_hyps s in
    let option = { Match.default_match_option with mode = `EntailRL } in
    let rec _deduce_all res goals =
      match goals with
      | [] -> res
      | e::after ->
        let biframe = List.rev_append res goals in
        let biframe_without_e = List.rev_append res after in
        let goal = Equiv.mk_equiv_atom biframe in
        let pat = Term.{
          pat_op_vars   = [];
          pat_op_tyvars = [];
          pat_op_term   = Equiv.mk_equiv_atom biframe_without_e;
        } in
        let match_result = 
          Match.E.try_match ~option ~hyps ~env:(ES.vars s) table system goal pat 
        in
        match match_result with
        | NoMatch _ -> _deduce_all (e::res) after 
        | Match mv -> 
          assert (Match.Mvar.is_empty mv);
          _deduce_all res after
    in
    let new_conclusion = List.rev (_deduce_all [] (ES.conclusion_as_equiv s)) in
    [ES.set_equiv_conclusion new_conclusion s]

(** Check whether the i^th element of the biframe is bideductible from the other ones, and 
    remove it if its the case. *)
let deduce_int (i : int L.located) s =
  let before, _, after = split_equiv_conclusion i s in
  let biframe_without_e = List.rev_append before after in
  let option = { Match.default_match_option with mode = `EntailRL } in
  let hyps = ES.get_trace_hyps s in 
  let table, system = ES.table s, ES.system s in
  let pat = Term.{
      pat_op_vars   = [];
      pat_op_tyvars = [];
      pat_op_term   = Equiv.mk_equiv_atom biframe_without_e;
    } in
  let conclusion = ES.conclusion s in
  let match_result = 
    Match.E.try_match ~option ~hyps ~env:(ES.vars s) table system conclusion pat 
  in
  match match_result with
  | NoMatch minfos -> soft_failure (ApplyMatchFailure minfos)
  | Match mv ->
    assert (Match.Mvar.is_empty mv);
    [ES.set_equiv_conclusion biframe_without_e s]

let deduce Args.(Opt (Int, p)) s : ES.sequents =
  match p with
  | None -> deduce_all s
  | Some (Args.Int i) -> deduce_int i s


let () =
  T.register_typed "deduce"
    ~pq_sound:true
    (LT.genfun_of_pure_efun_arg deduce) Args.(Opt Int)


(*------------------------------------------------------------------*)
let case_study arg s : ES.sequents =
  let l_proj, r_proj = ES.get_system_pair_projs s in

  (* Recursively project [if b then t1 else t2] to [f (t1,t2)].
     Does not project inside the branches of the projected conditionals.
     Returns the projected term, together with [found && p] where [p = true]
     iff some projection has been performed. *)
  let rec cs_proj
      f (b:Term.term) (found:bool) (t:Term.term) 
    : bool * Term.term 
    =
    let head = Term.head_normal_biterm [l_proj; r_proj] t in
    match head with
    | Term.App (Term.Fun (sy,_),[phi;t1;t2]) when phi = b
                                               && sy = Symbols.fs_ite ->
      true, f (t1,t2)
    | _ -> Term.tmap_fold (cs_proj f b) found t
  in

  let li, b =
    match arg with
    | Args.(Pair ((Message (b,Type.Boolean)), Opt (Int, i))) ->
      i, b
    | _ -> Tactics.(soft_failure 
                     (Failure "Argument of cs should match a boolean"))
  in
  match li with
  | None ->
    (* Project in all items. *)
    let founds,e1 =
      List.split
        (List.map (cs_proj fst b false) (ES.conclusion_as_equiv s)) in
    let e2 =
      List.map (fun t -> snd (cs_proj snd b false t)) (ES.conclusion_as_equiv s) in
    if not (List.exists (fun x -> x) founds) then
      Tactics.(soft_failure
                 (Failure "did not find any conditional to analyze")) ;
    [ES.set_equiv_conclusion (e1@[b]) s; ES.set_equiv_conclusion (e2@[b]) s]

  | Some (Args.Int i) ->
    (* Project in i-th item. *)
    let before, e, after = split_equiv_conclusion i s in
    let found,e1 = cs_proj fst b false e in
    let _,e2 = cs_proj snd b false e in
    if not found then
      Tactics.(soft_failure
                 (Failure "did not find any conditional to analyze")) ;
    [ES.set_equiv_conclusion (before@b::[e1]@after) s;
     ES.set_equiv_conclusion (before@b::[e2]@after) s]

let () =
  T.register_typed "cs"
    (LT.genfun_of_pure_efun_arg case_study) Args.(Pair(Message,Opt Int))

(*------------------------------------------------------------------*)
(** Fresh *)

let deprecated_fresh_mk_direct
    ((_n, n_args) : Term.nsymb * Term.terms)
    (occ : OldFresh.deprecated_name_occ) : Term.term
  =
  let bv, subst = Term.refresh_vars occ.occ_vars in
  let cond = List.map (Term.subst subst) occ.occ_cond in

  let cond = Term.mk_ands (List.rev cond) in
  
  let j = List.map (Term.subst subst) occ.occ_cnt in
  Term.mk_forall ~simpl:true bv
    (Term.mk_impl cond (Term.mk_neqs ~simpl_tuples:true n_args j))

let deprecated_fresh_mk_indirect
    (cntxt : Constr.trace_cntxt)
    (env : Vars.env)
    ((_n, n_args) : Term.nsymb * Term.terms)
    (frame_actions : OldFresh.deprecated_ts_occs)
    (occ : TraceTactics.deprecated_fresh_occ) : Term.term
  =  
  (* for each action [a] in which [name] occurs with indices from [occ] *)
  let bv = occ.Iter.occ_vars in
  let action, occ = occ.Iter.occ_cnt in

  assert ( Sv.subset
             (Action.fv_action action)
             (Sv.union (Vars.to_vars_set env) (Sv.of_list bv)));

  let bv, subst = Term.refresh_vars bv in

  (* apply [subst] to the action and to the list of
   * indices of our name's occurrences *)
  let action =
    SE.action_to_term cntxt.table cntxt.system
      (Action.subst_action subst action)
  in

  let occ = List.map (Term.subst subst) occ in

  (* condition stating that [action] occurs before a macro timestamp
     occurencing in the frame *)
  let disj = Term.mk_ors (OldFresh.deprecated_mk_le_ts_occs action frame_actions) in

  (* condition stating that indices of name in [action] and [name] differ *)
  let form = Term.mk_neqs ~simpl_tuples:true occ n_args in

  Term.mk_forall ~simpl:true bv (Term.mk_impl disj form)


(* kept for enckp and xor. *)
(** Construct the formula expressing freshness for some projection. *)
let deprecated_mk_phi_proj
    (cntxt : Constr.trace_cntxt)
    (hyps : TopHyps.TraceHyps.hyps)      (* initial hypotheses *)
    (venv : Vars.env)
    ((n,n_args) : Term.nsymb * Term.terms)
    (proj : Term.proj)
    (biframe : Term.term list) : Term.term list
  =
  let env = Env.init ~table:cntxt.table ~system:(SE.reachability_context cntxt.system) ~vars:venv () in
  let frame = List.map (Term.project1 proj) biframe in
  try
    let frame_indices : OldFresh.deprecated_name_occs =
      List.fold_left (fun acc t ->
          OldFresh.deprecated_get_name_indices_ext ~env cntxt n.s_symb t @ acc
        ) [] frame
    in
    let frame_indices = List.sort_uniq Stdlib.compare frame_indices in

    (* direct cases (for explicit occurrences of [name] in the frame) *)
    let phi_frame = List.map (deprecated_fresh_mk_direct (n,n_args)) frame_indices in

    let frame_actions : OldFresh.deprecated_ts_occs = OldFresh.deprecated_get_macro_actions cntxt frame in

    let macro_cases =
      TraceTactics.deprecated_mk_fresh_indirect_cases cntxt hyps venv n n_args biframe
    in

    (* indirect cases (occurrences of [name] in actions of the system) *)
    let phi_actions =
      List.fold_left (fun forms (_, cases) ->
          let cases =
            List.map
              (deprecated_fresh_mk_indirect cntxt venv (n,n_args) frame_actions)
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
  | OldFresh.Deprecated_Name_found ->
    soft_failure (Tactics.Failure "name not fresh")
  | OldFresh.Deprecated_Var_found ->
    soft_failure
      (Failure "cannot apply fresh: the formula contains a term variable")

let deprecated_fresh_cond (s : ES.t) t biframe : Term.term =
  let cntxt = mk_pair_trace_cntxt s in
  let env = ES.vars s in
  let hyps = ES.get_trace_hyps s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let n_left, n_left_args, n_right, n_right_args =
    match Term.project1 l_proj  t,
          Term.project1 r_proj t with
    | Name (nl, ll), Name (nr,lr) -> nl, ll, nr, lr
    | _ -> raise OldFresh.Deprecated_Not_name
  in

  let system_left = SE.project [l_proj] cntxt.system in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left =
    deprecated_mk_phi_proj cntxt_left hyps env (n_left, n_left_args) l_proj biframe 
  in

  let system_right = SE.project [r_proj] cntxt.system in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = 
    deprecated_mk_phi_proj cntxt_right hyps env (n_right, n_right_args) r_proj biframe 
  in

  let cstate = Reduction.mk_cstate cntxt.table in
  Term.mk_ands
    (* concatenate and remove duplicates *)
    (List.remove_duplicate (Reduction.conv cstate) (phi_left @ phi_right))



(*------------------------------------------------------------------*)
(** Automatic simplification *)

let conclusion_is_reach s =
  match ES.conclusion s with
  | Equiv.Atom (Reach _) -> true
  | _ -> false

let auto ~red_param ~strong ~close s sk (fk : Tactics.fk) =
  let rec auto_rec s sk fk =
    let open Tactics in
    match s with
    | Goal.Local t ->
      let sk l fk = sk (List.map (fun s -> Goal.Local s) l) fk in
      TraceTactics.simpl ~red_param ~close ~strong t sk fk

    | Goal.Global s when conclusion_is_reach s ->
      auto_rec (byequiv s) sk fk

    | Goal.Global s ->
      let sk l _ =
        sk (List.map (fun s -> Goal.Global s) l) fk
      and fk _ =
        if close
        then fk (None, GoalNotClosed)
        else sk [Goal.Global s] fk
      in
      (* old school fadup, simplifying the goal *)
      let wfadup s sk fk =
        if strong || (TConfig.auto_fadup (ES.table s)) then
          let fk _ = sk [s] fk in
          wrap_fail fa_dup s sk fk
        else sk [s] fk
      in
      (* more powerful bi-deduction, used to conclude proofs. *)
      let wdeduce s sk fk =
        if strong then
          let fk _ = sk [s] fk in
          wrap_fail deduce_all s sk fk
        else sk [s] fk
      in

      let conclude s sk fk  =
        if close then
          andthen_list ~cut:true
            [wrap_fail (EquivLT.expand_all_l `All);
             try_tac wdeduce;
             orelse_list [wrap_fail refl_tac;
                          wrap_fail assumption]] s sk fk
        else sk [s] fk
      in

      let reduce s sk fk =
        if strong
        then sk [EquivLT.reduce_sequent red_param s] fk
        else sk [s] fk
      in

      andthen_list ~cut:true
        [try_tac reduce;
         try_tac wfadup;
         conclude]
        s sk fk
  in
  auto_rec s sk fk
    
let equiv_auto ~red_param ~close ~strong s sk (fk : Tactics.fk) =
  auto ~red_param ~close ~strong s sk fk

let equiv_autosimpl s = 
  equiv_auto
    ~red_param:Reduction.rp_default
    ~close:false
    ~strong:false s


(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)


let global_diff_eq (s : ES.t) =
  let frame = ES.conclusion_as_equiv s in
  let system = Utils.oget (ES.system s).pair in
  let cntxt = mk_pair_trace_cntxt s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  (* Collect in ocs the list of diff terms that occur (directly or not)
     in [frame]. All these terms are relative to [system]. *)
  let ocs = ref [] in
  let iter (x : Symbols.action list) (y : Vars.vars) (t : Term.term) =
    (* rebuild a term with top-level diffs, before using 
       [simple_bi_term_no_alpha_find] to normalize it in a particular way. *)
    let t = Term.mk_diff [l_proj, Term.project1 l_proj t;
                          r_proj, Term.project1 r_proj t] in
    ocs := ( List.map (fun u -> (x,y,u))
               (Iter.get_diff ~cntxt (Term.simple_bi_term_no_alpha_find [l_proj; r_proj] t)))
           @ !ocs 
  in
  List.iter (iter [] []) frame;

  SE.iter_descrs cntxt.table system
  (fun action_descr ->
     let miter = iter [action_descr.Action.name] action_descr.Action.indices in
     miter (snd action_descr.Action.output) ;
     miter (snd action_descr.Action.condition) ;
     List.iter (fun (_,args,m) ->
         List.iter miter args;
         miter m
       ) action_descr.Action.updates) ;

  (* Function converting each occurrence to the corresponding subgoal. *)
  let subgoal_of_occ (vs,is,t) =
    let is = List.map Term.mk_var is in
    
    let cond = Term.mk_ands (List.rev t.Iter.occ_cond) in
    match t.Iter.occ_cnt with
    | Term.Diff (Explicit [p1,s1; p2,s2]) as subterm
      when p1 = l_proj && p2 = r_proj ->
        let fvars =
          t.Iter.occ_vars @ Sv.elements (Term.fv subterm)
        in
        let pred_ts_list =
          let iter = new OldFresh.deprecated_get_actions ~cntxt in
          iter#visit_message subterm;
          iter#visit_message cond;
          iter#get_actions
        in
        (* Remark that the get_actions add pred to all timestamps, to simplify. *)
        let ts_list = 
          (List.map (fun v -> Term.mk_action v is) vs)
          @ List.map (function
              | Term.App (Term.Fun (fs, _), [tau]) when fs = Term.f_pred -> tau
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
          Term.add_vars_env (ES.vars s) (Vars.Tag.global_vars (Sv.elements fv_ts_list))
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
        Goal.Global
          (ES.set_conclusion
             (* TODO: we assume that the variables are global and constant. 
                It is not clear that this is correct: check this when the tactic 
                is reworked. *)
             (Equiv.Smart.mk_forall_tagged (Vars.Tag.global_vars ~const:true fvars)
                (Equiv.mk_reach_atom 
                   (Term.mk_impls 
                      (List.map Term.mk_happens ts_list
                       @ List.map (fun t -> Term.mk_macro Term.exec_macro [] t) ts_list
                       @ [cond])
                      (Term.mk_atom `Eq s1 s2))
                ))
             s
          )
    | _ -> assert false
  in
  List.map subgoal_of_occ !ocs

let () =
  T.register "diffeq"
    ~pq_sound:true
    (LT.genfun_of_efun global_diff_eq)


(*------------------------------------------------------------------*)
(** implement the SplitSeq rule of CSF'21, modified when moving
    to the higher-order logic. *)
let split_seq (li : int L.located) (htcond : Theory.term) ~else_branch s : ES.sequent =
  let before, t, after = split_equiv_conclusion li s in
  let i = L.unloc li in

  (* no differences between seq and lambda, except that we keep using a sequence 
     if we start with a sequence*)
  let is, ti, is_seq = match t with
    | Quant (Seq,    is, ti) -> is, ti, true
    | Quant (Lambda, is, ti) -> is, ti, false
    | _ ->
      soft_failure ~loc:(L.loc li) (Failure (string_of_int i ^ " is not a seq or a lambda"))
  in

  (* check that types are compatible *)
  let seq_hty = Type.fun_l (List.map Vars.ty is) Type.Boolean in

  let htcond, hty = EquivLT.convert s htcond in

  check_ty_eq hty seq_hty;

  (* compute the new sequent *)
  let is, subst = Term.refresh_vars is in
  let ti = Term.subst subst ti in

  let is_terms = List.map Term.mk_var is in

  let cond = Term.mk_app htcond is_terms in

  (* The value of the else branch is the user-supplied value, if any.
     Otherwise, we choose a value according to the type *)
  let else_branch =
    match else_branch with
    | Some t ->
      let t, _ =
        let cntxt = Theory.{ env = ES.env s; cntxt = InGoal; } in
        Theory.convert ~ty:(Term.ty ti) ~pat:false cntxt t
      in
      t

    | None ->
      match Term.ty ti with
      | Type.Message -> Term.mk_zero
      | Type.Boolean -> Term.mk_false
      | ty           -> Term.Prelude.mk_witness (ES.table s) ~ty_arg:ty
  in

  let ti_t = Term.mk_ite cond               ti else_branch in
  let ti_f = Term.mk_ite (Term.mk_not cond) ti else_branch in

  let mk_seq_or_lambda = if is_seq then Term.mk_seq else Term.mk_lambda in

  let frame = List.rev_append before ([mk_seq_or_lambda is ti_t;
                                       mk_seq_or_lambda is ti_f] @ after) in
  ES.set_equiv_conclusion frame s

let split_seq_args args s : ES.sequent list =
  match args with
  | [Args.SplitSeq (i, ht, else_branch)] -> [split_seq i ht ~else_branch s]
  | _ -> bad_args ()

let split_seq_tac args = wrap_fail (split_seq_args args)

let () =
  T.register_general "splitseq"
    (LT.gentac_of_etac_arg split_seq_tac)

(*------------------------------------------------------------------*)
let mem_seq (i_l : int L.located) (j_l : int L.located) s : Goal.t list =
  let before, t, after = split_equiv_conclusion i_l s in
  let _, seq, _ = split_equiv_conclusion j_l s in

  let seq_vars, seq_term = match seq with
    | Quant ((Seq | Lambda), vs, t) -> vs, t
    | _ ->
      soft_failure ~loc:(L.loc j_l)
        (Failure (string_of_int (L.unloc j_l) ^ " is not a seq or a lambda"))
  in

  check_ty_eq (Term.ty t) (Term.ty seq_term);

  (* refresh the sequence *)
  let seq_vars, subst = Term.refresh_vars seq_vars in
  let seq_term = Term.subst subst seq_term in

  let subgoal =
    let form =
      Term.mk_exists ~simpl:true seq_vars
        (Term.mk_atom `Eq t seq_term)
    in
    let trace_s = ES.to_trace_sequent (ES.set_reach_conclusion form s) in
    Goal.Local trace_s
  in

  let frame = List.rev_append before after in
  [subgoal; Goal.Global (ES.set_equiv_conclusion frame s)]

let mem_seq_args args s : Goal.t list =
  match args with
  | [Args.MemSeq (i, j)] -> mem_seq i j s
  | _ -> bad_args ()

let mem_seq_tac args = wrap_fail (mem_seq_args args)

let () =
  T.register_general "memseq"
    (LT.genfun_of_efun_arg mem_seq_tac)

(*------------------------------------------------------------------*)
(** implement the ConstSeq rule of CSF'21, modified when moving to the higher-order logic. *)
let const_seq
    ((li, b_t_terms) : int L.located * (Theory.term * Theory.term) list)
    (s : ES.t) : Goal.t list
  =
  let before, e, after = split_equiv_conclusion li s in
  let i = L.unloc li in

  let e_is, e_ti = match e with
    | Quant ((Seq | Lambda), is, ti) -> is, ti
    | _ ->
      soft_failure ~loc:(L.loc li) 
        (Failure (string_of_int i ^ " is not a seq or a lambda"))
  in
  let b_t_terms : (Term.term * Term.term) list =
    List.map (fun (p_bool, p_term) ->
        let t_bool, b_ty = EquivLT.convert s p_bool in
        let term, term_ty = EquivLT.convert s p_term in
        let p_bool_loc = L.loc p_bool in

        (* check that types are compatible *)
        let seq_hty = Type.fun_l (List.map Vars.ty e_is) Type.Boolean in
        check_ty_eq ~loc:p_bool_loc b_ty seq_hty;

        check_ty_eq ~loc:(L.loc p_term) term_ty (Term.ty e_ti);

        (* check that [p_bool] is a const+SI formula *)
        if not (HighTerm.is_ptime_deducible ~si:true (ES.env s) t_bool) then
          hard_failure ~loc:p_bool_loc
            (Failure "conditions must be ptime and system-independent");

        t_bool, term
      ) b_t_terms
  in

  (* refresh variables *)
  let e_is, subst = Term.refresh_vars e_is in
  let e_ti = Term.subst subst e_ti in

  (* instantiate all boolean [hterms] in [b_t_terms] using [e_is] *)
  let e_is_terms = List.map Term.mk_var e_is in
  let b_t_terms : (Term.term * Term.term) list =
    List.map (fun (t_bool, term) ->
        Term.mk_app t_bool e_is_terms, term
      ) b_t_terms
  in

  (* first sub-goal: (∀ e_is, ∨ᵢ bᵢ *)
  let cases = Term.mk_ors ~simpl:true (List.map fst b_t_terms) in
  let cond1 = Term.mk_forall ~simpl:true e_is cases in
  let subg1 = ES.set_reach_conclusion cond1 s |> ES.to_trace_sequent in

  (* second sub-goal: (∧ᵢ (∀ e_is, bᵢ → tᵢ = e_ti) *)
  let eqs = List.map (fun (t_bool, term) ->
      Term.mk_forall ~simpl:true e_is
        (Term.mk_impl t_bool (Term.mk_atom `Eq e_ti term))
    ) b_t_terms
  in
  let cond2 = Term.mk_ands ~simpl:true eqs in
  let subg2 = ES.set_reach_conclusion cond2 s |> ES.to_trace_sequent in

  (* third sub-goal *)
  let terms = List.map snd b_t_terms in
  let frame = List.rev_append before (terms @ after) in

  [ Goal.Local subg1;
    Goal.Local subg2;
    Goal.Global (ES.set_equiv_conclusion frame s) ]

let const_seq_args args s : Goal.t list =
  match args with
  | [Args.ConstSeq (i, t)] -> const_seq (i, t) s
  | _ -> bad_args ()

let const_seq_tac args = wrap_fail (const_seq_args args)

let () =
  T.register_general "constseq"
    (LT.genfun_of_efun_arg const_seq_tac)


(*------------------------------------------------------------------*)
(** Encryption key privacy  *)

let enckp arg (s : ES.t) =
  let i, m1, m2 =
    match arg with
    | Args.(Pair (Int i, Pair (Opt (Message, m1), Opt (Message, m2)))) ->
      i, m1, m2
    | _ -> assert false
  in
  let before, e, after = split_equiv_conclusion i s in

  let biframe = List.rev_append before after in
  let cntxt = mk_pair_trace_cntxt s in
  let table = cntxt.table in
  let env = ES.env s in
  let l_proj, r_proj = ES.get_system_pair_projs s in

  (* Apply tactic to replace key(s) in [enc] using [new_key].
   * Precondition:
   * [enc = Term.Fun (fnenc, [Tuple [m; Term.Name r; k])]].
   * Verify that the encryption primitive is used correctly,
   * that the randomness is fresh and that the keys satisfy their SSC. *)
  let apply_kp
      ~(enc     : Term.term)
      ~(new_key : Term.term option)
      ~(fnenc   : Symbols.fname)
      ~(m       : 'b)
      ~(r       : Name.t)
      ~(k       : Term.term)
    : Goal.t list 
    =
    let k = Term.head_normal_biterm [l_proj; r_proj] k in
    (* Verify that key is well-formed, depending on whether the encryption is
     * symmetric or not. Return the secret key and appropriate SSC. *)
    let ssc, wrap_pk, sk =
      if Symbols.is_ftype fnenc Symbols.SEnc table then
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             let env = Env.update ~system:SE.{ set = (system :> SE.t); pair = None } env in

             Oldcca.deprecated_symenc_key_ssc
               ~cntxt fnenc fndec
               ~elems:(ES.conclusion_as_equiv s) sk.Name.symb.s_symb;
             Oldcca.deprecated_symenc_rnd_ssc
               ~cntxt env fnenc ~key:sk.Name.symb ~key_is:sk.Name.args biframe),
          (fun x -> x),
          k
        | _ -> assert false

      else
        match Symbols.Function.get_data fnenc table with
        | Symbols.AssociatedFunctions [fndec;fnpk] ->
          (fun (sk,system) ->
             let cntxt = Constr.{ cntxt with system } in
             let errors =
               (* TODO: set globals to true *)
               OldEuf.key_ssc ~globals:false
                 ~cntxt ~elems:(ES.conclusion_as_equiv s)
                 ~allow_functions:(fun x -> x = fnpk) fndec sk.Name.symb.s_symb
             in
             if errors <> [] then
               soft_failure (Tactics.BadSSCDetailed errors)),
          (fun x -> Term.mk_fun table fnpk [x]),
          begin match k with
            | Term.App (Term.Fun (fnpk', _), [sk])
              when fnpk = fnpk' -> sk
            | Term.App (Term.Fun (fnpk', _), [sk])
              when fnpk = fnpk' -> sk
            | _ ->
              soft_failure
                (Failure
                   "The first encryption is not used \
                    with the correct public key function")
          end
        | _ -> assert false

    in
    let project = function
      | Term.Name _ as n -> Name.of_term n, Name.of_term n
      | Term.(Diff (Explicit [_, (Name _ as l); _, (Name _ as r)])) ->
        Name.of_term l, Name.of_term r
      | _ -> soft_failure (Failure "Secret keys must be names")
    in

    let skl, skr = project sk in
    let (new_skl, new_skr), new_key =
      match new_key with
      | Some k -> project k, k
      | None -> (skl, skl), Term.mk_name skl.symb skl.args
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
        deprecated_fresh_cond s (Term.mk_name r.symb r.args) (context@biframe)
      with Oldcca.Bad_ssc -> soft_failure Tactics.Bad_SSC
    in
    let fresh_goal =
      s |> ES.set_reach_conclusion random_fresh_cond |> ES.to_trace_sequent
    in

    (* Equivalence goal where [enc] is modified using [new_key]. *)
    let new_enc =
      Term.mk_fun_tuple table fnenc [m; Term.mk_name r.symb r.args; wrap_pk new_key]
    in
    let new_elem =
      Equiv.subst_equiv [Term.ESubst (enc,new_enc)] [e]
    in
    let biframe = (List.rev_append before (new_elem @ after)) in

    [Goal.Local fresh_goal;
     Goal.Global (ES.set_equiv_conclusion biframe s)]

  in

  let target,new_key = match m1,m2 with
    | Some (Message (m1, _)), Some (Message (m2, _)) ->
      Some m1, Some m2

    | Some (Message (m1, _)), None ->
      begin match m1 with
        | Term.App (Fun (_f,_),[Tuple [_;_;_]]) -> Some m1, None
        | _ -> None, Some m1
      end
    | None, None -> None, None
    | None, Some _ -> assert false
  in

  match target with
  | Some (Term.App (Term.Fun (fnenc, _), [Tuple [m; Term.Name _ as r; k]]) as enc) ->
    apply_kp ~enc ~new_key ~fnenc ~m ~r:(Name.of_term r) ~k
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
      | Term.Diff _ | Term.App (Term.Fun (_, _), [Term.Diff _]) -> true
      | _ -> false
    in

    let rec find = function
      | occ :: occs ->
        if not (occ.Iter.occ_vars = []) then find occs
        else
        begin match occ.Iter.occ_cnt with
          | Term.App (Term.Fun (fnenc, _), [Tuple [m; Term.Name _ as r; k]]) as enc
            when diff_key k ->
            apply_kp ~enc ~new_key ~fnenc ~m ~r:(Name.of_term r) ~k

          | _ -> find occs
        end

      | [] ->
        soft_failure
          (Tactics.Failure ("no subterm of the form enc(_,r,k) where \
                             r is a name and k contains a diff(_,_)"))
    in find encs

let () =
  T.register_typed "enckp"
    ~pq_sound:true
    (LT.genfun_of_efun_arg enckp)
    Args.(Pair (Int, Pair (Opt Message,Opt Message)))

(*------------------------------------------------------------------*)
(** XOR *)

(* Removes the first occurence of Name (n,is) in the list l. *)
let remove_name_occ (n,a) l = match l with
  | [Term.Name (n',a'); t] when (n,a) = (n',a') -> t
  | [t; Term.Name (n',a')] when (n,a) = (n',a') -> t
  | _ ->
    Tactics.(soft_failure (Failure "name is not XORed on both sides"))

let mk_xor_phi_base (s : ES.t) biframe
    ((n_left, n_left_args), l_left, (n_right, n_right_args), l_right, _term) =
  let cntxt = mk_pair_trace_cntxt s in
  let env   = ES.vars  s in
  let hyps  = ES.get_trace_hyps s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  
  let biframe =
    Term.mk_diff [l_proj,l_left;r_proj,l_right] :: biframe
  in

  let system_left = SE.project [l_proj] cntxt.system in
  let cntxt_left = { cntxt with system = system_left } in
  let phi_left = 
    deprecated_mk_phi_proj cntxt_left hyps env (n_left, n_left_args) l_proj biframe 
  in

  let system_right = SE.project [r_proj] cntxt.system in
  let cntxt_right = { cntxt with system = system_right } in
  let phi_right = 
    deprecated_mk_phi_proj cntxt_right hyps env (n_right, n_right_args) r_proj biframe 
  in

  let len_left =
    Term.(mk_eq (mk_len l_left) (mk_len (mk_name n_left n_left_args)))
  in

  let len_right =
    Term.(mk_eq (mk_len l_right) (mk_len (mk_name n_right n_right_args)))
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
    | (Term.App (Fun (fl,_),_ll), App (Fun (fr,_),_lr))
      when (fl = Term.f_xor && fr = Term.f_xor) -> true
    | _ -> false
  in
  let is_name_diff mess_name =
    match Term.project1 l_proj  mess_name,
          Term.project1 r_proj mess_name with
    | Name _, Name _ -> true
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
  let before, e, after = split_equiv_conclusion i s in

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

  let (n_left, n_left_args), l_left, 
      (n_right, n_right_args), l_right, term =
    match opt_n with
    | None ->
      begin
        match Term.project1 l_proj  t,
              Term.project1 r_proj t with
        | (App (Fun (fl, _), [Term.Name (nl, al);ll]),
           App (Fun (fr, _), [Term.Name (nr, ar);lr]))
          when (fl = Term.f_xor && fr = Term.f_xor) ->
          ((nl,al),ll,(nr,ar),lr,t)

        | _ -> soft_failure (Failure "ill-formed arguments")
      end
    | Some mess_name ->
      begin
        match Term.project1 l_proj  mess_name,
              Term.project1 r_proj mess_name with
        | Name (nl,al), Name (nr,ar) ->
          begin match Term.project1 l_proj t,
                      Term.project1 r_proj t with
            | (App (Fun (fl,_),ll), App (Fun (fr,_),lr))
              when (fl = Term.f_xor && fr = Term.f_xor) ->
              ((nl,al),remove_name_occ (nl,al) ll,
               (nr,ar),remove_name_occ (nr,ar) lr,
               t)
            | _ -> soft_failure (Failure "ill-formed arguments")
          end
        | _ -> soft_failure (Failure "ill-formed arguments")
      end
  in
  let phi =
    mk_xor_phi_base s biframe
      ((n_left, n_left_args), l_left, (n_right, n_right_args), l_right, term)
  in
  let n_fty = Type.mk_ftype [] [] Message in
  let ndef = Symbols.{ n_fty } in
  let sym = (L.mk_loc L._dummy "n_XOR") in
  let table,n =
    Symbols.Name.declare (ES.table s) sym ndef
  in
  let real_name = L.mk_loc L._dummy (Symbols.to_string n) in
  let table = 
    Process.add_namelength_axiom table real_name n_fty in

  let ns = Term.mk_symb n Message in
  let s = ES.set_table table s in

  let then_branch = Term.mk_name ns [] in
  let else_branch = term in
  let if_term = Term.mk_ite phi then_branch else_branch in

  let new_elem =
    Equiv.subst_equiv [Term.ESubst (t,if_term)] [e]
  in
  let biframe = List.rev_append before (new_elem @ after) in
  [ES.set_equiv_conclusion biframe s]


let () =
  T.register_typed "xor"
   ~pq_sound:true
   (LT.genfun_of_pure_efun_arg xor)
   Args.(Pair (Int, Pair (Opt Message, Opt Message)))


(*------------------------------------------------------------------*)
exception Not_context

class ddh_context
    ~(cntxt:Constr.trace_cntxt) ~gen ~exp ~l_proj ~r_proj exact a b c
  = object (_self)

 inherit Iter.deprecated_iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms args a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
      | Symbols.(Input | Output | State _ | Cond | Exec | Frame) -> ()
      | _ -> super#visit_macro ms args a

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
    | Term.(App (Fun (f1,_), [(App (Fun (f2,_), [g1; Name (n1,_)])); Name (n2,_)])),
      Term.(App (Fun (_f, _), [g3; Name (n3,_)])) 
      when f1 = exp && f2 = exp && g1 = gen && g3 = gen && n3.s_symb = c &&
           ((n1.s_symb = a && n2.s_symb = b) ||
            (n1.s_symb = b && n2.s_symb = a)) -> ()

    | _ ->
      match t with
      (* any name n can occur as g^n *)
      | Term.App (Term.Fun (f, _), [g1; Name _]) when f = exp && g1 = gen -> ()

      (* if a name a, b, c appear anywhere else, fail *)
      | Term.Name (n,_) when List.mem n.s_symb [a; b; c] -> raise Not_context

      (* if a diff is not over a valid ddh diff, we fail  *)
      | Term.Diff _ -> raise Not_context

      | _ -> super#visit_message t

end

(*------------------------------------------------------------------*)
exception Macro_found

class find_macros ~(cntxt:Constr.trace_cntxt) exact = object (self)
 inherit Iter.deprecated_iter_approx_macros ~exact ~cntxt as super

  method visit_macro ms args a =
    match Symbols.Macro.get_def ms.s_symb cntxt.table with
    | Symbols.(Input | Output | State _ | Cond | Exec | Frame) ->
      raise Macro_found
    | _ -> self#visit_macro ms args a
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
        List.iter (fun (_,args,t) ->
            List.iter iter#visit_message args;
            iter#visit_message t
          ) d.updates;
    );
   (* we then check inside the frame *)
    List.iter iter#visit_message elem_list;
    true
  with Not_context | OldFresh.Deprecated_Name_found -> false

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
    | Symbols.AssociatedFunctions [exp       ] -> exp
    | Symbols.AssociatedFunctions [exp; _mult] -> exp
    | _ -> assert false
  in

  let gen = Term.mk_fun tbl gen_symb [] in
  let exp = exp_symb in

  let cntxt = mk_pair_trace_cntxt s in
  let l_proj, r_proj = ES.get_system_pair_projs s in
  if is_ddh_context ~gen ~exp ~cntxt ~l_proj ~r_proj
       na nb nc (ES.conclusion_as_equiv s)
  then sk [] fk
  else soft_failure Tactics.NotDDHContext

(* DDH is called on strings that correspond to names, put potentially without
   the correct arity. E.g, with name a(i), we need to write ddh a, .... Thus, we
   cannot use the typed registering, as a is parsed as a name identifier, which
   then does not have the correct arity. *)

let () =
  T.register_general "ddh"
    (function
       | [Args.String_name gen;
          Args.String_name v1;
          Args.String_name v2;
          Args.String_name v3] ->
         LT.gentac_of_etac (ddh gen v1 v2 v3)
       | _ -> bad_args ())

(*------------------------------------------------------------------*)
let crypto (game : lsymb) (args : Args.crypto_args) (s : ES.t) =
  let frame = ES.conclusion_as_equiv s in
  let subgs = Crypto.prove (ES.env s) (ES.get_trace_hyps s) game args frame in
  List.map (fun subg -> ES.set_reach_conclusion subg s) subgs
  
let crypto_tac args (s : ES.t) =
  match args with
  | [Args.Crypto (game, args)] -> wrap_fail (crypto game args) s
  | _ -> bad_args ()

let () =
  T.register_general "crypto"
    (LT.gentac_of_etac_arg crypto_tac)
