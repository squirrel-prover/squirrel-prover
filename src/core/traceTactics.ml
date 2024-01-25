(** All reachability tactics.
   Tactics are organized in three classes:
    - Logical -> relies on the logical properties of the sequent.
    - Structural -> relies on properties of protocols, or of equality over
      messages,...
    - Cryptographic -> relies on a cryptographic assumptions, that must be
      assumed.
*)
open Term
open Utils

module T    = ProverTactics
module Args = HighTacticsArgs
module L    = Location
module SE   = SystemExpr

module LT = LowTactics

module TS = TraceSequent

module TopHyps = Hyps
(* module Hyps = TS.LocalHyps *)

type tac = TS.t Tactics.tac
type lsymb = Theory.lsymb
type sequent = TS.sequent

module Sp = Match.Pos.Sp
              
(*------------------------------------------------------------------*)
open LowTactics

(*------------------------------------------------------------------*)
let wrap_fail = TraceLT.wrap_fail

let hard_failure = Tactics.hard_failure
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
let true_intro (s : TS.t) =
  match TS.conclusion s with
  | tt when tt = Term.mk_true -> []
  | _ -> soft_failure (Tactics.Failure "Cannot introduce true")

let () =
  T.register "true"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun true_intro)

(*------------------------------------------------------------------*)
(** Case analysis on [orig = Find (vars,c,t,e)] in [s].
  * This can be used with [vars = []] if orig is an [if-then-else] term. *)
let case_cond orig vars c t e s : sequent list =
  let vars, subst = Term.refresh_vars vars in
  let then_c = Term.subst subst c in
  let else_c = Term.mk_forall vars (Term.mk_not then_c) in

  let then_t = Term.subst subst t in
  let else_t = e in

  let mk_case case_vars case_t case_cond : sequent =
    let case_subst =
      if case_vars = [] then [Term.ESubst (orig, case_t)] else []
    in

    let prem =
      Term.mk_exists
        case_vars
        (Term.mk_and ~simpl:false
           case_cond
           (Term.mk_atom `Eq orig case_t))
    in

    let case_conclusion =
      Term.mk_impl ~simpl:false
        prem
        (Term.subst case_subst (TS.conclusion s))
    in
    TS.set_conclusion case_conclusion s
  in

  [ mk_case vars then_t then_c;
    mk_case    [] else_t else_c]

let conditional_case (m : Term.term) s : sequent list =
  match m with
  | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
  | Term.App (Term.Fun (f,_),[c;t;e]) when f = Term.f_ite ->
    case_cond m [] c t e s

  | Term.Macro (ms,args,ts) ->

    if not (TS.query_happens ~precise:true s ts) then
      soft_failure (Tactics.MustHappen ts);

    begin
      match Macros.get_definition_exn (TS.mk_trace_cntxt s) ms ~args ~ts with
      | Term.Find (vars,c,t,e) -> case_cond m vars c t e s
      | Term.App (Term.Fun (f,_),[c;t;e]) when f = Term.f_ite ->
        case_cond m [] c t e s
      | _ -> Tactics.(soft_failure (Failure "message is not a conditional"))
    end

  | _ ->
    Tactics.(soft_failure (Failure "message is not a conditional"))

let boolean_case b s : sequent list =
  let do_one b_case b_val =
    let g = Term.subst [Term.ESubst (b, b_val)] (TS.conclusion s) in
    TS.set_conclusion (Term.mk_impl ~simpl:false b_case g) s
  in
  [ do_one b Term.mk_true;
    do_one (Term.mk_not ~simpl:false b) Term.mk_false]

(*------------------------------------------------------------------*)
let do_case_tac (args : Args.parser_arg list) s : sequent list =
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
  | Some str when TS.Hyps.mem_name (L.unloc str) s && structure_based ->
    let id, f = TS.Hyps.by_name_k str Hyp s in

    (* check that [str] is a local hypothesis *)
    check_local ~loc:(L.loc str) f;
    
    List.map
      (fun (TraceLT.CHyp _, ss) -> ss)
      (TraceLT.hypothesis_case ~nb:`Any id s)

  | _ ->
    match TraceLT.convert_args s args Args.(Sort Term) with
    | Args.Arg (Term (ty, f, _)) ->
      begin
        match ty with
        | Type.Timestamp when type_based -> TraceLT.timestamp_case f s
        | Type.Boolean   when type_based -> boolean_case   f s
        | _ when structure_based -> conditional_case f s
        | _ -> bad_args ()
      end

    | _ -> bad_args ()

let case_tac args = wrap_fail (do_case_tac args)

(*------------------------------------------------------------------*)

let rec simpl_left (s : TS.t) =
  let func (id,ldc) =
    match ldc with
    | TopHyps.LHyp (Equiv.Local (Fun (fs, _) as t))
      when fs = Term.f_false || fs = Term.f_and ->
      Some (id,t)
    | TopHyps.LHyp (Equiv.Local (Term.Quant (Exists, _, _) as t)) -> Some (id,t)
    | _ -> None
    (* legacy behavior: global hypotheses are not modified *)
  in

  match TS.Hyps.find_map func s with
  | None -> Some s
  | Some (id, f) ->
    begin
      match f with
      | tf when tf = Term.mk_false -> None

      | Term.Quant (Exists,vs,f) ->
        let s = TS.Hyps.remove id s in
        let env = ref @@ TS.vars s in
        let subst =
          List.map
            (fun v ->
               Term.ESubst (Term.mk_var v,
                            Term.mk_var (Vars.make_approx_r env v (Vars.Tag.make Vars.Local))))
            vs
        in
        let f = Term.subst subst f in
        simpl_left (TS.Hyps.add Args.AnyName (LHyp (Local f)) (TS.set_vars !env s))

      | _ as form ->
        let f, g = oget (Term.destr_and form) in
        let s = TS.Hyps.remove id s in
        simpl_left
          (TS.Hyps.add_list [(Args.AnyName, LHyp (Local f));
                             (Args.AnyName, LHyp (Local g))] s)
    end
    
let simpl_left_tac s =
  match simpl_left s with
  | None -> []
  | Some s -> [s]

(*------------------------------------------------------------------*)
(** [any_assumption s] succeeds (with no subgoal) if the sequent [s]
    can be proved using the axiom rule (plus some other minor rules). 
    If [hyp = Some id], only checks for hypothesis [id]. *)
let assumption ?hyp (s : TS.t) = 
  let conclusion = TS.conclusion s in
  let assumption_entails (id, f) = 
    (hyp = None || hyp = Some id) &&
    match f with
    | TopHyps.LHyp (Equiv.Global (Equiv.Atom (Reach f)))
    | TopHyps.LHyp (Equiv.Local f) ->
      TS.Reduce.conv_term s conclusion f ||
      List.exists (fun f ->
          TS.Reduce.conv_term s conclusion f ||
          TS.Reduce.conv_term s f Term.mk_false
        ) (decompose_ands f)
    | TopHyps.LHyp (Equiv.Global _) | TopHyps.LDef _ -> false
  in
  if conclusion = Term.mk_true ||
     TS.Hyps.exists assumption_entails s
  then begin
    dbg "assumption %a" Term.pp conclusion;
    []
  end else soft_failure Tactics.NotHypothesis

let do_assumption_tac args (s : TS.t) : TS.t list =
  let hyp =
    match Args.convert_as_lsymb args with
    | Some str -> Some (fst (TS.Hyps.by_name_k str Hyp s))
    | None -> None 
  in
  assumption ?hyp s

let assumption_tac args = wrap_fail (do_assumption_tac args)

(*------------------------------------------------------------------*)
(** [localize h h' s sk fk] succeeds with a single subgoal if
    the sequent [s] has a global hypothesis [h] which is a reachability
    atom.
    The generated subgoal is identical to [s] but with a new local
    hypothesis [h'] corresponding to that atom. *)
let localize h h' s =
  match TS.Hyps.by_name_k h Hyp s with
    | _,Global (Equiv.Atom (Reach f)) ->
        [TS.Hyps.add h' (LHyp (Local f)) s]
    | _ ->
        Tactics.(soft_failure (Failure "cannot localize this hypothesis"))
    | exception Not_found ->
        Tactics.(soft_failure (Failure "no hypothesis"))

let () =
  T.register_general "localize"
    ~pq_sound:true
    (function
       | TacticsArgs.[String_name h; NamingPat h'] ->
           fun s sk fk ->
             begin match LowTactics.genfun_of_pure_tfun (localize h h') s with
               | subgoals -> sk subgoals fk
               | exception (Tactics.Tactic_soft_failure e) -> fk e
             end
       | _ -> assert false)

(*------------------------------------------------------------------*)
(** {2 Structural Tactics} *)

(*------------------------------------------------------------------*)
(** [congruence judge sk fk] try to close the goal using congruence, else
    calls [fk] *)
let congruence (s : TS.t) : bool =
  match simpl_left s with
  | None -> true
  | Some s ->
    let conclusions =
      Utils.odflt [] (Term.Lit.disjunction_to_literals (TS.conclusion s))
    in

    let term_conclusions =
      List.fold_left (fun acc conc -> 
          Term.Lit.lit_to_form (Term.Lit.neg conc) :: acc
        ) [] conclusions
    in
    let s = List.fold_left (fun s f ->
        TS.Hyps.add Args.Unnamed (LHyp (Local f)) s
      ) s term_conclusions
    in
    TS.eq_atoms_valid s

(** [congruence s] proves the sequent using its message equalities,
    up to equational theories. *)
let congruence_tac (s : TS.t) =
  match congruence s with
  | true ->
    let () = dbg "closed by congruence" in
    []

  | false ->
    let () = dbg "congruence failed" in
    soft_failure Tactics.CongrFail

let () =
  T.register "congruence"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun congruence_tac)

(*------------------------------------------------------------------*)
let constraints (s : TS.t) =
  match simpl_left s with
  | None -> true
  | Some s ->
    let s =
      TS.Hyps.add Args.Unnamed
        (LHyp (Local (Term.mk_not (TS.conclusion s))))
        (TS.set_conclusion Term.mk_false s)
    in
    TS.constraints_valid s

(** [constraints s] proves the sequent using its trace formulas. *)
let constraints_ttac (s : TS.t) =
  let s = as_seq1 (TraceLT.intro_all s) in
  match constraints s with
  | true ->
    let () = dbg "closed by constraints" in
    []

  | false ->
   let () = dbg "constraints failed" in
   soft_failure (Tactics.Failure "constraints satisfiable")

let constraints_tac args : LT.ttac = 
  match args with
  | [] -> wrap_fail constraints_ttac
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
(** Check if [v] type can be assume to be [const] in [s]. 
    Use the fact that for finite types which do not depend on the 
    security parameter η, we have
    [∀ x, phi] ≡ ∀ x. const(x) → [phi]
    (where the RHS quantification is a global quantification) *)
let strengthen_const_var (s : TS.t) (v : Vars.var) : bool =
  let table = TS.table s in
  if Symbols.TyInfo.is_finite table (Vars.ty v) && 
     Symbols.TyInfo.is_fixed  table (Vars.ty v) then

    (* check that [v] does not appear in any global hypothesis or definitions *)
    TS.Hyps.fold (fun _ hyp b ->
        match hyp with
        | LHyp (Equiv.Local _) -> b
        | LDef (_,t) -> b && not (Sv.mem v (Term.fv t))
        | LHyp (Equiv.Global f) -> 
          b && not (Sv.mem v (Equiv.fv f))
      ) s true

  else false

(*------------------------------------------------------------------*)
(** Try to add the [const] tag to all variables of the sequent.
    Added in [simpl]. *)
let strengthen_const_vars (s : TS.t) : TS.t =
  let vars = 
    Vars.map_tag (fun v tag ->
        { tag with const = tag.const || strengthen_const_var s v } 
      ) (TS.vars s) 
  in
  TS.set_vars vars s

(*------------------------------------------------------------------*)
let const_tac (Args.Term (ty, f, loc)) (s : TS.t) =
  let table = TS.table s in

  if not (Symbols.TyInfo.is_finite table ty && 
          Symbols.TyInfo.is_fixed  table ty   ) then
    soft_failure ~loc
      (Failure "only applies to finite and fixed (η-independent) types");

  let v = 
    match f with 
    | Var v -> v
    | _ -> soft_failure ~loc (Failure "must be a variable");
  in

  let to_lower = 
    TS.Hyps.fold (fun id hyp to_lower -> 
        match hyp with
        | LHyp (Equiv.Local _) -> to_lower

        | LHyp (Equiv.(Global (Atom (Reach hyp)))) -> 
          if Sv.mem v (Term.fv hyp) then (id, hyp) :: to_lower else to_lower

        | LHyp (Equiv.Global hyp) -> 
          if Sv.mem v (Equiv.fv hyp) then 
            soft_failure ~loc
              (Failure 
                 (Fmt.str "%a appears in non-localizable hypothesis %a \
                           (clear the hypothesis?)"
                    Vars.pp v Ident.pp id))
          else to_lower

        | LDef (_,t) -> 
          if Sv.mem v (Term.fv t) then 
            soft_failure ~loc
              (Failure 
                 (Fmt.str "%a appears in definition %a \
                           (revert it?)"
                    Vars.pp v Ident.pp id))
          else to_lower
      ) s []
  in
 
  if to_lower <> [] then
    Printer.prt `Warning 
      "@[<hov 2>localize:@ %a@]" 
      (Fmt.list ~sep:Fmt.sp Ident.pp) (List.map fst to_lower);

  let s = TS.Hyps.filter (fun (id, _) -> not (List.mem_assoc id to_lower)) s in
  let s = 
    let to_lower = 
      List.map
        (fun (id,hyp) -> (Args.Named (Ident.name id), TopHyps.LHyp (Equiv.Local hyp)) ) 
        to_lower 
    in
    TS.Hyps.add_list to_lower s
  in
  [strengthen_const_vars s]

let () =
  T.register_typed "const"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg const_tac)
    Args.((Term : _ sort))

(*------------------------------------------------------------------*)
(** Eq-Indep Axioms *)

(* We include here rules that are specialization of the Eq-Indep axiom. *)

(** Add index constraints resulting from names equalities, modulo the TRS.
    The judgment must have been completed before calling [eq_names]. *)
let eq_names (s : TS.t) =
  let table = TS.table s in
  let env   = TS.env   s in

  let add_hyp s c =
    let () = dbg "new equalities (eqnames): %a" Term.pp c in
    TS.Hyps.add Args.Unnamed (LHyp (Local c)) s
  in

  (* we now collect equalities between timestamp implied by equalities between
     names. *)
  let trs = TS.get_trs s in
  let cnstrs =
    Completion.name_index_cnstrs table trs (TS.get_all_messages s)
  in
  let s =
    List.fold_left (fun (s : sequent) ((n1,l1),(n2,l2)) ->
        (* we have [n1 l1 = n2 l2] *)
        if List.for_all (HighTerm.is_constant env) (l1 @ l2) then
          if n1 <> n2 then
            add_hyp s Term.mk_false
          else            
            List.fold_left2 (fun s t1 t2 ->
                match t1, t2 with
                | Tuple l1, Tuple l2 ->
                  List.fold_left add_hyp s (List.map2 Term.mk_eq l1 l2)
                | _ -> add_hyp s (Term.mk_eq t1 t2)
              ) s l1 l2
        else 
          s
      ) s cnstrs
  in
  [s]

let () =
  T.register "eqnames"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun eq_names)

(*------------------------------------------------------------------*)
(* no longer used for fresh. 
   left here temporarily, for compatibility *)
(** triple of the action and the name indices *)
type deprecated_fresh_occ = (Action.action * Term.terms) Iter.occ

(** check if all instances of [o1] are instances of [o2].
    [o1] and [o2] actions must have the same action name *)
let deprecated_fresh_occ_incl
    table system
    (o1 : deprecated_fresh_occ) (o2 : deprecated_fresh_occ) : bool 
  =
  (* for now, positions not allowed here *)
  assert (Sp.is_empty o1.occ_pos && Sp.is_empty o2.occ_pos);
  
  let a1, is1 = o1.occ_cnt in
  let a2, is2 = o2.occ_cnt in

  let cond1 = Term.mk_ands (List.rev o1.occ_cond)
  and cond2 = Term.mk_ands (List.rev o2.occ_cond) in

  (* build a dummy term, which we used to match in one go all elements of
     the two occurrences *)
  let mk_dum a is cond =
    let action = SE.action_to_term table system a in
    Term.mk_ands ~simpl:false
      ((Term.mk_atom `Eq Term.init action) ::
       (Term.mk_ands (List.map2 (Term.mk_eq ~simpl:false) is is)) ::
       [cond])
  in
  let pat2 = Term.{
      pat_op_tyvars = [];
      pat_op_vars   = Vars.Tag.local_vars o2.occ_vars;
      pat_op_term   = mk_dum a2 is2 cond2;
    }
  in

  let context = SE.reachability_context system in
  match Match.T.try_match table context (mk_dum a1 is1 cond1) pat2 with
  | Match.NoMatch _ -> false
  | Match.Match   _ -> true

(** Add a new fresh rule case, if it is not redundant. *)
let deprecated_add_fresh_case
    table system
    (c : deprecated_fresh_occ)
    (l : deprecated_fresh_occ list) : deprecated_fresh_occ list
  =
  if List.exists (fun c' -> deprecated_fresh_occ_incl table system c c') l
  then l
  else
    (* remove any old case which is subsumed by [c] *)
    let l' =
      List.filter (fun c' ->
          not (deprecated_fresh_occ_incl table system c' c)
        ) l
    in
    c :: l'

(** Add many new fresh rule cases, if they are not redundant. *)
let deprecated_add_fresh_cases
    table system
    (l1 : deprecated_fresh_occ list)
    (l2 : deprecated_fresh_occ list) : deprecated_fresh_occ list
  =
  List.fold_left (fun l2 c -> deprecated_add_fresh_case table system c l2) l2 l1

(* Indirect cases - names ([n],[is']) appearing in actions of the system *)
let deprecated_mk_fresh_indirect_cases
    (cntxt : Constr.trace_cntxt)
    (hyps : Hyps.TraceHyps.hyps)      (* initial hypotheses *)
    (venv : Vars.env)
    (ns : Term.nsymb)
    (ns_args : Term.terms)
    (terms : Term.term list)
  =
  (* sanity check: free variables in [ns] and [terms] are included in [env] *)
  assert (
    let all_fv =
      List.fold_left (fun s t ->
          Sv.union s (Term.fv t)
        ) (Term.fvs ns_args) terms
    in
    Sv.subset all_fv (Vars.to_vars_set venv));

  let env = Env.init ~table:cntxt.table ~system:(SE.reachability_context cntxt.system) ~vars:venv () in

  let macro_cases =
    Iter.fold_macro_support (fun iocc macro_cases ->
        let action_name = iocc.iocc_aname  in
        let a           = iocc.iocc_action in
        let t           = iocc.iocc_cnt    in
        
        let fv =
          Sv.diff
            (Sv.union (Action.fv_action a) (Term.fv t))
            (Vars.to_vars_set venv)
        in

        let new_cases =
          let fv = List.rev (Sv.elements fv) in
          OldFresh.deprecated_get_name_indices_ext ~env:env ~fv cntxt ns.s_symb t
        in
        let new_cases =
          List.map (fun (case : OldFresh.deprecated_name_occ) ->
              { case with
                occ_cnt = (a, case.occ_cnt);
                occ_cond = case.occ_cond; }
            ) new_cases
        in

        List.assoc_up_dflt action_name []
          (fun l ->
             deprecated_add_fresh_cases cntxt.table cntxt.system new_cases l
          ) macro_cases
      ) cntxt env hyps terms []
  in
  (* we keep only action names in which the name occurs *)
  List.filter (fun (_, occs) -> occs <> []) macro_cases


(*------------------------------------------------------------------*)
let apply_substitute subst s =
    let s =
    match subst with
      | Term.ESubst (Term.Var v, t) :: _ when
        not (List.mem v (Term.get_vars t)) ->
          TS.set_vars (Vars.rm_var v (TS.vars s)) s
      | _ -> s
  in
  [TS.subst subst s]

let substitute_mess (m1, m2) s =
  let subst =
        let trs = TS.get_trs s in
        if Completion.check_equalities trs [(m1,m2)] then
          [Term.ESubst (m1,m2)]
        else
          soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_ts (ts1, ts2) s =
  let subst =
      if TS.query ~precise:true s [(`Pos, Comp (`Eq,ts1,ts2))] then
        [Term.ESubst (ts1,ts2)]
      else
        soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_idx (i1 , i2 : Term.term * Term.term) s =
  let i1, i2 =  match i1, i2 with
    | Var _, Var _ -> i1, i2
    | (Diff _), _ | _, (Diff _) ->
      hard_failure
        (Tactics.Failure "only variables are supported when substituting \
                          index terms")
    | _ -> assert false
  in

  let subst =
    if TS.query ~precise:true s [(`Pos, Comp (`Eq,i1,i2))] then
      [Term.ESubst (i1,i2)]
    else
      soft_failure Tactics.NotEqualArguments
  in
  apply_substitute subst s

let substitute_tac arg s =
  let open Args in
  match arg with
  | Pair (Term (Type.Message, f1, _), Term (Type.Message, f2, _)) ->
    substitute_mess (f1,f2) s

  | Pair (Term (Type.Timestamp, f1, _), Term (Type.Timestamp, f2, _)) ->
    substitute_ts (f1,f2) s

  | Pair (Term (Type.Index, f1, _), Term (Type.Index, f2, _)) ->
    substitute_idx (f1,f2) s

  | _ ->
    hard_failure
      (Tactics.Failure "expected a pair of messages, booleans or a pair of \
                        index variables")

let () =
  T.register_typed "subst"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg substitute_tac)
    Args.(Pair (Term, Term))

(*------------------------------------------------------------------*)
(* TODO: this should be an axiom in some library, not a rule *)
let exec (Args.Message (a,_)) s =
  let _,var = Vars.make `Approx (TS.vars s) Type.Timestamp "t" TS.var_info in
  let formula =
    Term.mk_forall ~simpl:false
      [var]
      (Term.mk_impl
         (Term.mk_timestamp_leq (mk_var var) a)
         (mk_macro Term.exec_macro [] (mk_var var)))
  in
  [TraceLT.happens_premise s a ;

   TS.set_conclusion (Term.mk_macro exec_macro [] a) s;

    TS.set_conclusion
      (Term.mk_impl ~simpl:false formula (TS.conclusion s)) s]

let () =
  T.register_typed "executable"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg exec)
    Args.Timestamp


(*------------------------------------------------------------------*)
(** [fa s] handles some goals whose conclusion formula is of the form
    [C(u_1..u_N) = C(v_1..v_N)] and reduced them to the subgoals with
    conclusions [u_i=v_i]. We only implement it for the constructions
    [C] that congruence closure does not support: conditionals,
    sequences, etc. *)
let fa s =
  let table = TS.table s in

  let unsupported () = soft_failure (Failure "equality expected") in

  let check_vars vars vars' =
    if List.length vars <> List.length vars' then
      soft_failure (Failure "FA: sequences with different lengths");

    let tys_compatible = 
      List.for_all2 (fun v1 v2 -> 
          Type.equal (Vars.ty v1) (Vars.ty v2)
        ) vars vars'
    in
    if not tys_compatible then
      soft_failure (Failure "FA: sequences with different types");
  in

  let u, v = match TS.Reduce.destr_eq s Local_t (TS.conclusion s) with
    | Some (u,v) -> u, v
    | None -> unsupported ()
  in
  match u,v with
  | Term.App (Term.Fun (f,_),[c;t;e]), Term.App (Term.Fun (f',_),[c';t';e'])
    when f = Term.f_ite && f' = Term.f_ite ->
    let subgoals =
      let open TraceSequent in
      [ s |> set_conclusion (Term.mk_impl c c') ;

        s |> set_conclusion (Term.mk_impl c' c) ;

        s |> set_conclusion (Term.mk_impls
                         (if TS.Reduce.conv_term s c c' then [c] else [c;c'])
                         (Term.mk_atom `Eq t t'));

        s |> set_conclusion (Term.mk_impls
                         [Term.mk_not c;
                          Term.mk_not c']
                         (Term.mk_atom `Eq e e')) ]
    in
    subgoals

  (* FIXME: allow ForAll and Exists? *)
  | Term.Quant (Seq, vars,t), Term.Quant (Seq, vars',t')
    when List.for_all (Symbols.TyInfo.is_finite table -| Vars.ty) vars -> 
    check_vars vars vars';

    (* refresh variables *)
    let vars, t =
      let vars, subst = Term.refresh_vars vars in
      vars, Term.subst subst t
    in
    let vars', t' =
      let vars', subst = Term.refresh_vars vars' in
      vars', Term.subst subst t'
    in
    
    (* have [t'] use the same variables names than [t] *)
    let t' = 
      let subst = 
        List.map2 (fun v' v -> 
            Term.ESubst (Term.mk_var v', Term.mk_var v)
          ) vars' vars
      in
      Term.subst subst t'
    in

    let env = TS.vars s in
    let env, _, subst =         (* add variables as local vars. *)
      Term.add_vars_env env (List.map (fun v -> v, TS.var_info) vars)
    in 
    let s = TS.set_vars env s in
    let t = Term.subst subst t in
    let t' = Term.subst subst t' in
    let subgoals =
      [ TS.set_conclusion (Term.mk_atom `Eq t t') s ]
    in
    subgoals

  | Term.Find (vs,c,t,e),
    Term.Find (vars',c',t',e')
    when List.for_all (Symbols.TyInfo.is_finite table -| Vars.ty) vs &&
         List.length vs = List.length vars' ->
    (* We verify that [e = e'],
     * and that [t = t'] and [c <=> c'] for fresh index variables.
     *
     * We do something more general for the conditions,
     * which is useful for cases arising from diff-equivalence
     * where some indices are unused on one side:
     *
     * Assume [vars = used@unused]
     * where [unusued] variables are unused in [c] and [t].
     *
     * We verify that [forall used. (c <=> exists unused. c')]:
     * this ensures that if one find succeeds, the other does
     * too, and also that the selected indices will match
     * except for the [unused] indices on the left, which does
     * not matter since they do not appear in [t]. *)

    (* Refresh bound variables in c and t *)
    let env = TS.vars s in
    let env, vars, subst =    (* add variables as local vars. *)
      Term.add_vars_env env (List.map (fun v -> v, TS.var_info) vs) 
    in
    let c  = Term.subst subst c in
    let t  = Term.subst subst t in

    (* Create substitution from vars' to fresh_var *)
    (* We avoid relying on the fact that currently, subst is preserving
       the order of vars, and rather create a substitution vs -> vars',
       that we apply on the lhs of vs -> vars *)

    let subst_aux = List.map2 (fun x y ->
        Term.(ESubst (mk_var x,mk_var y))) vs vars' in
    let subst' = List.map (function ESubst (x, y) ->
        Term.(ESubst (subst subst_aux x,y))) subst in

    let s = TS.set_vars env s in

    let c' = Term.subst subst' c' in

    let t' = Term.subst subst' t' in

    (* Extract unused variables. *)
    let _used,unused =
      let occ_vars = Term.get_vars c @ Term.get_vars t in
      List.partition
        (fun v -> List.mem v occ_vars)
        vars
    in

    let subgoals =
      let open TraceSequent in
      [ set_conclusion (Term.mk_impl c (Term.mk_exists unused c')) s ;

        set_conclusion (Term.mk_impl c' c) s;

        set_conclusion (Term.mk_impls [c;c']
                    (mk_atom `Eq t t')) s;

        set_conclusion (Term.mk_atom `Eq e e') s]
    in
    subgoals

  | _ -> Tactics.(soft_failure (Failure "unsupported equality"))

let fa_tac args = match args with
  | [] -> wrap_fail fa
  | _ -> bad_args ()

(*------------------------------------------------------------------*)
(** New goal simplification *)

let new_simpl ~red_param ~congr ~constr s =
  let s = TraceLT.reduce_sequent red_param s in
  let s = strengthen_const_vars s in

  let goals = Term.decompose_ands (TS.conclusion s) in
  let s = TS.set_conclusion Term.mk_false s in
  let goals = List.filter_map (fun goal ->
      if TS.Hyps.is_hyp (Local goal) s || Term.f_triv goal then None
      else match Term.Lit.form_to_xatom goal with
        | None -> Some goal
        | Some at ->
          match at, Term.Lit.ty_xatom at with
          | _, Type.Index | _, Type.Timestamp -> 
            let lit = `Pos, (at :> Term.Lit.xatom) in
            if constr && TS.query ~precise:true s [lit]
            then None
            else Some goal

          | Comp (`Eq, t1, t2), _ ->
            if congr &&
               Completion.check_equalities (TS.get_trs s) [(t1,t2)]
            then None
            else Some goal

          | _ -> Some goal
    ) goals in
  [TS.set_conclusion (Term.mk_ands goals) s]


(*------------------------------------------------------------------*)
(** Automated goal simplification *)

let clear_triv s sk fk = sk [TS.Hyps.clear_triv s] fk

(** Simplify goal. *)
let _simpl ~red_param ~close ~strong =
  let open Tactics in

  let assumption = if close then [try_tac (wrap_fail assumption)] else [] in

  let strengthen_const_vars s sk fk = sk [strengthen_const_vars s] fk in

  let new_simpl ~congr ~constr =
    if strong
    then [wrap_fail (new_simpl ~red_param ~congr ~constr)] @ assumption
    else []
  in

  let expand_all =
    (if strong && close
     then [wrap_fail (TraceLT.expand_all_l `All)] @ assumption
     else [])
  in


  andthen_list ~cut:true (
    [strengthen_const_vars] @
    (* Try assumption first to avoid loosing the possibility
       * of doing it after introductions. *)
    assumption @
    (new_simpl ~congr:false ~constr:false) @
    (if close then [wrap_fail TraceLT.intro_all;
                    wrap_fail simpl_left_tac] else []) @
    assumption @
    expand_all @
    (if strong then [wrap_fail eq_names] else []) @
    expand_all @
    assumption @ (new_simpl ~congr:true ~constr:true) @
    [clear_triv]
  )

(*------------------------------------------------------------------*)
(* Attempt to close a goal. *)
let do_conclude =
  Tactics.orelse_list [wrap_fail congruence_tac;
                       wrap_fail constraints_ttac;
                       wrap_fail assumption]



(* If [close] then tries to automatically prove the goal,
 * otherwise it may also be reduced to a single subgoal. *)
let simpl ~red_param ~strong ~close : TS.t Tactics.tac =
  let rec simpl_aux ~close = 
    let open Tactics in
    let (>>) = andthen ~cut:true in
    (* if [close], we introduce as much as possible to help. *)
    _simpl ~red_param ~strong ~close >>

    if not strong
    then (fun g sk fk -> sk [g] fk)
    else
      (if close
       then try_tac do_conclude else Tactics.id) >>
      fun g sk fk ->
      (* If we still have a goal, we can try to split a conjunction
       * and prove the remaining subgoals, or return this goal,
       * but we must respect [close]. *)
      let fk =
        if close
        then fun _ -> fk (None, GoalNotClosed)
        else fun _ -> sk [g] fk
      in
      (wrap_fail TraceLT.and_right) g
        (fun l _ -> match l with
           | [g1;g2] ->
             simpl_aux ~close g1
               (fun l' _ ->
                  if l'=[] then
                    simpl_aux ~close g2 sk fk
                  else
                    simpl_aux ~close:true g2
                      (fun l'' fk -> assert (l'' = []) ; sk l' fk)
                      fk)
               fk
           | _ -> assert false)
        fk
  in
  simpl_aux ~close
    
let trace_auto ~red_param ~strong ~close s sk (fk : Tactics.fk) =
  simpl ~red_param ~close ~strong s sk fk

let trace_autosimpl s =
  trace_auto
    ~red_param:Reduction.rp_default
    ~close:false
    ~strong:false
    s


(* tries to close the goal with simpl *)
(* returns true if the goal was closed, false otherwise *)
let tryauto_closes (g:sequent) : bool =
  (* exception to get out of the continuations *)
  let exception Res of bool in
  let red_param = Reduction.rp_default in
  try
    let _:Tactics.a =
      simpl ~red_param ~strong:true ~close:true g
        (* if simpl succeeds: it closes the goal, so l = [] *)
        (fun l _ -> assert (l = []); raise (Res true)) 
        (* otherwise: leave the goal unchanged *)
        (fun _ -> raise (Res false))
    in
    assert false (* impossible: simpl never returns, it runs its continuations *)
  with
  | Res b -> b
   

(* returns gs without the goals that can be closed automatically *)
let tryauto (gs:sequent list) : sequent list =
  List.filter (fun g -> not (tryauto_closes g)) gs



(*------------------------------------------------------------------*)
(** Projecting a goal on a bi-system
  * to distinct goals for each projected system. *)

let project s =
  match SE.to_list (SE.to_fset (TS.system s).set) with
  | [_] ->
    soft_failure (Tactics.Failure "goal already deals with a \
                                           single process")
  | l ->
    List.map (fun (lbl,_) -> TS.pi lbl s) l

let () =
  T.register "project"
    ~pq_sound:true
     (LowTactics.genfun_of_pure_tfun project)

(*------------------------------------------------------------------*)
(** {2 Cryptographic Tactics} *)
   

(*------------------------------------------------------------------*)
let valid_hash (cntxt : Constr.trace_cntxt) (t : Term.term) =
  match t with
  | Term.App (Fun (hash, _), [Tuple [_msg; Name (_key, _)]]) ->
    Symbols.is_ftype hash Symbols.Hash cntxt.table

  | _ -> false

(** We collect all hashes appearing inside the hypotheses, and which satisfy
    the syntactic side condition. *)
let top_level_hashes s =
  let cntxt = TS.mk_trace_cntxt s in

  let hashes =
    List.filter (valid_hash cntxt) (TS.get_all_messages s)
    |> List.sort_uniq Stdlib.compare
  in

  if List.length hashes = 0 then soft_failure Tactics.NoSSC;

  let rec make_eq acc hash_list =
    match hash_list with
    | [] -> acc
    | h1::q ->
      List.fold_left
        (fun acc h2 ->
           match h1, h2 with
           | Term.App (Fun (hash1, _), [Tuple [_; Name (key1,args1)]]),
             Term.App (Fun (hash2, _), [Tuple [_; Name (key2,args2)]])
             when hash1 = hash2 && (key1,args1) = (key2,args2) ->
             (h1, h2) :: acc
           | _ -> acc)
        (make_eq acc q) q
  in

  let trs = TS.get_trs s in

  make_eq [] hashes
  |> List.filter (fun (a,b) ->
      Completion.check_equalities trs [(a,b)])



(** [collision_resistance arg judge sk fk]
    applies the collision resistance axiom between the hashes:
    - if [arg = Some h], collision in hypothesis [j]
    - if [arg = None], collects all equalities between hashes that occur at
    toplevel in message hypotheses. *)
let collision_resistance TacticsArgs.(Opt (String, arg)) (s : TS.t) = 
  let hash_eqs =
    match arg with
    | None -> top_level_hashes s
    | Some (String p_h) ->
      let _, h = TS.Hyps.by_name_k p_h Hyp s in
      let h = as_local ~loc:(L.loc p_h) h in
      match TS.Reduce.destr_eq s Local_t h with
      | Some (t1, t2) ->
        let cntxt = TS.mk_trace_cntxt s in
        if not (valid_hash cntxt t1) || not (valid_hash cntxt t2) then
          soft_failure Tactics.NoSSC;

        [t1,t2]
      | _ -> soft_failure Tactics.NoCollision
  in

  let new_facts =
    List.fold_left
      (fun acc (h1,h2) ->
         match h1, h2 with
         | Term.App (Fun (hash1, _), [Tuple [m1; Name (key1,args1)]]),
           Term.App (Fun (hash2, _), [Tuple [m2; Name (key2,args2)]])
           when hash1 = hash2 && (key1,args1) = (key2,args2) ->
           Term.mk_atom `Eq m1 m2 :: acc
         | _ -> acc)
      [] hash_eqs
  in
  let f_coll = Term.mk_ands new_facts in

  if f_coll = Term.mk_true then soft_failure Tactics.NoCollision;

  let goal = Term.mk_impl ~simpl:false f_coll (TS.conclusion s) in
  [TS.set_conclusion goal s]

let () =
  T.register_typed "collision"
    ~pq_sound:true
    (LowTactics.genfun_of_pure_tfun_arg collision_resistance)
    Args.(Opt String)

(*------------------------------------------------------------------*)

(** Transform a term according to some equivalence given as a biframe.
  * Macros in the term occurring (at toplevel) on the [src] projection
  * of some biframe element are replaced by the corresponding [dst]
  * projection. *)
let rewrite_equiv_transform
    ~(src:Term.proj)
    ~(dst:Term.proj)
    ~(s:TS.t)
    (biframe : Term.term list)
    (term : Term.term) : Term.term option
  =
  let exception Invalid in

  let assoc (t : Term.term) : Term.term option =
    match List.find_opt (fun e -> 
        TS.Reduce.conv_term s (Term.project1 src e) t
      ) biframe 
    with
    | Some e -> Some (Term.project1 dst e)
    | None -> None
  in
  let rec aux (t : term) : term = 
    match Term.ty t with
    | Type.Timestamp | Type.Index when
        HighTerm.is_ptime_deducible ~si:true (TS.env s) t -> t
    (* system-independence needed, so that we leave [t] unchanged when the system do *)
      
    | _ ->
      match assoc t with
      | None -> aux_rec t
      | Some t' -> t'

  and aux_rec (t : Term.term) : Term.term = 
    match t with
    | t when HighTerm.is_ptime_deducible ~si:true (TS.env s) t -> t
    (* system-independence needed, so that we leave [t] unchanged when the system do *)

    | Term.App (f,args) -> Term.mk_app (aux f) (List.map aux args)

    | Diff (Explicit l) ->
      Term.mk_diff (List.map (fun (p,t) -> p, aux t) l)

    (* We can support input@ts (and keep it unchanged) if
     * for some ts' such that ts'>=pred(ts),
     * frame@ts' is a biframe element, i.e. the two
     * projections are frame@ts'.
     * Note that this requires that ts' and pred(ts)
     * happen, which is necessary to have input@ts =
     * att(frame@pred(ts)) and frame@pred(ts) a sublist
     * of frame@ts'. *)
    | Macro (msymb,_,ts) when msymb = Term.in_macro ->
      let ok_frame = function
        | Macro (msymb',[],ts') ->
          msymb' = Term.frame_macro &&
          TS.query ~precise:true s
            [`Pos,Comp (`Leq, mk_pred ts, ts')]
        | _ -> false
      in
      if List.exists ok_frame biframe then t else raise Invalid

    | _ -> raise Invalid
  in
  try Some (aux term) with Invalid -> None

(* Rewrite equiv rule on sequent [s] with direction [dir],
   using assumption [ass] wrt system [ass_context]. *)
let rewrite_equiv (ass_context,ass,dir) (s : TS.t) : TS.t list =

  (* Decompose [ass] as [subgoal_1 => .. => subgoal_N => equiv(biframe)].
     We currently require subgoals to be reachability formulas,
     for simplicity. *)
  let subgoals, biframe =
    let rec aux = function
      | Equiv.(Atom (Equiv bf)) -> [],bf
      | Impl (Atom (Reach f),g) -> let s,bf = aux g in f::s,bf
      | _ -> Tactics.soft_failure (Failure "invalid assumption")
    in aux ass
  in

  (* Subgoals are relative to [ass_context.set].
     They are proved in theory as global formulas, immediately changed in
     the tactic to local formulas. These local formulas cannot be proved
     while keeping all local hypotheses: however, we can keep the pure trace
     formulas from the local hypotheses.
     We already know that [ass_context.set] is compatible with the systems
     used in the equivalence, hence we keep [s]'s context. *)
  let s' =
    s |>
    TS.Hyps.filter
      (fun (_,ldc) ->
         match ldc with
         | LDef _ -> true
         (* definition have their own local context, hence their semantics remain unchanged *)
           
         | LHyp (Local f) -> 
           HighTerm.is_constant     (TS.env s) f &&
           HighTerm.is_system_indep (TS.env s) f
         | LHyp (Global _) -> true)
  in
  let subgoals = List.map (fun f -> TS.set_conclusion f s') subgoals in

  (* Identify which projection of the assumption's conclusion
     corresponds to the current goal and new goal (projections [src,dst])
     and the expected systems before and after the transformation. *)
  let src,dst,orig_sys,new_sys =
    let pair = Utils.oget ass_context.SE.pair in
    let left,lsys = SE.fst pair in
    let right,rsys = SE.snd pair in
    match dir with
      | `LeftToRight -> left,right,lsys,rsys
      | `RightToLeft -> right,left,rsys,lsys
  in

  (* Compute new set annotation, checking by the way
     that rewrite equiv applies to sequent [s]. *)
  let updated_set =
    SE.to_list (SE.to_fset (TS.system s).set) |>
    List.map (fun (p,s) ->
                if s = orig_sys then p, new_sys else
                  Tactics.(soft_failure Rewrite_equiv_system_mismatch)) |>
    SE.of_list
  in
  let updated_context =
    { (TS.system s) with set = (updated_set:>SE.arbitrary) } in

  let warn_unsupported t =
    Printer.prt `Warning
      "Cannot transform %a: it will be dropped.@." Term.pp t
  in

  (* Attempt to transform. If the transformation can't
   * be applied we can simply drop the hypothesis rather
   * than failing completely. *)
  let rewrite (h : Term.term) : Term.term option =
    match rewrite_equiv_transform ~src ~dst ~s biframe h with
    | None -> warn_unsupported h; None
    | x -> x
  in

  let goal =
    TS.set_conclusion_in_context
      ~update_local:rewrite
      updated_context
      (match rewrite_equiv_transform ~src ~dst ~s biframe (TS.conclusion s) with
       | Some t -> t
       | None -> warn_unsupported (TS.conclusion s); Term.mk_false)
      s
  in
  subgoals @ [goal]

let rewrite_equiv_args args (s : TS.t) : TS.t list =
  match args with
  | [TacticsArgs.RewriteEquiv rw] ->
    let ass_context, subgs, ass, dir = TraceLT.p_rw_equiv rw s in
    subgs @ rewrite_equiv (ass_context, ass, dir) s
  | _ -> bad_args ()

let rewrite_equiv_tac args = wrap_fail (rewrite_equiv_args args)

let () =
  T.register_general "rewrite equiv"
    ~pq_sound:true
    (LowTactics.gentac_of_ttac_arg rewrite_equiv_tac)