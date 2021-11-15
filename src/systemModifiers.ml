open Utils

module SE   = SystemExpr
module L    = Location

let global_rename table sdecl gf =
  let env,vars = Theory.convert_p_bnds table [] Vars.empty_env [] in
  let conv_env = Theory.{ table; cntxt = InGoal } in

  let f = Theory.convert_global_formula conv_env [] env gf in

  let ns1, ns2, n1, n2 =
    match f with
    | Quant (ForAll, _, Atom (Equiv ([
        Term.Diff (Term.Name ns1, Term.Name ns2)
      ]
      )) )
    |  Atom (Equiv ([Term.Diff (Term.Name ns1, Term.Name ns2)]))
        ->  ns1, ns2, Term.mk_name ns1, Term.mk_name ns2
    | _ -> assert false

  in
  let old_system = match SE.parse_se table sdecl.Decl.from_sys  with
    | Single s as res -> res
    | _ -> assert false
  in

  (* We check that n2 does not occur in the old system using fresh. *)
  let cntxt = Constr.{table=table;
                          system= old_system;
                          models=None}
  in
  let iter = new  Fresh.find_name ~cntxt true ns2.s_symb in
  try
    SystemExpr.iter_descrs cntxt.table cntxt.system (
      fun action_descr ->
        iter#visit_message (snd action_descr.Action.output) ;
        iter#visit_message (snd action_descr.Action.condition) ;
        List.iter (fun (_,m) -> iter#visit_message m) action_descr.Action.updates);

    (* We now build the rewrite rule *)
    let evars = Term.get_vars n1 in
    let vs, subs = Term.erefresh_vars `Global evars in
    let (n1', n2') = (Term.subst subs n1, Term.subst subs n2) in
    let rw_rule = Rewrite.{
        rw_tyvars = [];
        rw_vars = Vars.Sv.of_list vs;
        rw_conds = [];
        rw_rw = Term.ESubst (n1', n2');
      }
    in
    let iterator cenv t =
      match
        Rewrite.rewrite table old_system env TacticsArgs.(`Once)
          rw_rule (`Reach t)
      with
      | `Result (`Reach res, ls) -> res
      | _ -> t
    in
    try
      (* We now declare the system *)
      let table, new_system =
        SystemExpr.clone_system_iter
          table old_system
          sdecl.Decl.name (Action.apply_descr iterator) in

      (* We finally put as axiom the equivalence between the old and the new system *)
      let new_system_expr,old_system_expr, old_system_name = match old_system with
        | Single (Left s as old) -> SE.Left new_system, old, s
        | Single (Right s as old) -> SE.Right new_system, old, s
        |  _ -> assert false
      in

      let new_system_e = SystemExpr.pair table old_system_expr new_system_expr in
      let axiom_name = "rename_from_"^(Symbols.to_string old_system_name)
                       ^"_to_"^(Location.unloc sdecl.name) in

      (* we now create the lhs of the obtained conclusion *)
      let fresh_x_var = Vars.make_new Type.Message "mess" in
      let enrich = [Term.mk_var fresh_x_var] in
      let make_conclusion equiv = `Equiv
          Equiv.(Quant (ForAll, [EVar fresh_x_var],
                        Impl(
                          Quant (ForAll, evars,
                                 Atom (
                                   Equiv [Term.mk_var fresh_x_var; Term.mk_diff n1 n2]
                                 )
                                )
                        , equiv)
                       )
                       )
      in
      (axiom_name, enrich, make_conclusion, new_system_e, table)
    with SystemExpr.SystemNotFresh ->
      Tactics.hard_failure
        (Tactics.Failure "System name already defined for another system.")

  with Fresh.Name_found -> Tactics.hard_failure
                             (Tactics.Failure "The name on the right-hand side already occurs in the left-hand side.")


let global_prf table sdecl ty_vars hash =
  let env,vars = Theory.convert_p_bnds table [] Vars.empty_env ty_vars in
  let conv_env = Theory.{ table; cntxt = InGoal } in
  let hash, _ = Theory.convert_i conv_env [] env hash in
  let is =  (List.map (fun x -> Vars.ecast x Type.KIndex) vars) in


  let env = ref env in
  let old_system = match SE.parse_se table sdecl.Decl.from_sys  with
    | Single s as res -> res
    | _ -> assert false
  in

  let cntxt = Constr.{table=table;
                      system= old_system;
                      models=None}
  in

  let param = Prf.prf_param hash in
  (* Check syntactic side condition. *)
  let errors =
    Euf.key_ssc
      ~elems:[] ~allow_functions:(fun x -> false)
      ~cntxt param.h_fn param.h_key.s_symb
  in
  if errors <> [] then
    Tactics.soft_failure (Tactics.BadSSCDetailed errors);

  (* We first refresh globably the indices to create the left pattern*)
  let is1, left_subst = Term.refresh_vars (`Global) is in

  let left_key =  Term.subst left_subst (Term.mk_name param.h_key) in
  let left_key_ids = match left_key with
    | Term.Name s -> s.s_indices
    | _ -> assert false
  in
  (* We create the pattern for the hash *)
  let fresh_x_var = Vars.make_new Type.Message "x" in
  let hash_pattern = Term.mk_fun table param.h_fn [] [Term.mk_var fresh_x_var;
                                                   left_key ] in

  (* Instantiation of the fresh name *)
  let ndef = Symbols.{ n_iarr = List.length is; n_ty = Message ; } in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_PRF") ndef
  in
  (* the hash h of a message m will be replaced by tryfind is s.t = fresh mess
     in fresh else h *)
  let mk_tryfind =
        let ns = Term.mk_isymb n Message (is) in
        Term.mk_find is Term.(
            mk_and
              (mk_atom `Eq (Term.mk_var fresh_x_var) param.h_cnt)
              (mk_indices_eq left_key_ids param.h_key.s_indices)
          ) (Term.mk_name ns) hash_pattern
  in
  let rw_rule = Rewrite.{
    rw_tyvars = [];
    rw_vars = Vars.Sv.of_list ((Vars.evar fresh_x_var)::(List.map Vars.evar is1));
    rw_conds = [];
    rw_rw = Term.ESubst (hash_pattern, mk_tryfind);
  }
  in

  let iterator cenv t =
    match
      Rewrite.rewrite table old_system (!env) TacticsArgs.(`Once)
        rw_rule (`Reach t)
    with
    | `Result (`Reach res, ls) -> res
    | _ -> t
  in

 try
    let table, new_system =
      SystemExpr.clone_system_iter
        table old_system
        sdecl.Decl.name (Action.apply_descr iterator) in

      (* We finally put as axiom the equivalence between the old and the new system *)
      let new_system_expr,old_system_expr, old_system_name = match old_system with
        | Single (Left s as old) -> SE.Left new_system, old, s
        | Single (Right s as old) -> SE.Right new_system, old, s
        |  _ -> assert false
      in

      let new_system_e = SystemExpr.pair table old_system_expr new_system_expr in
      let axiom_name = "prf_from_"^(Symbols.to_string old_system_name)
                       ^"_to_"^(Location.unloc sdecl.name)
      in

      (* we now create the lhs of the obtained conclusion *)
      let fresh_x_var = Vars.make_new Type.Message "mess" in
      let enrich = [Term.mk_var fresh_x_var] in
      let make_conclusion equiv = `Equiv
          Equiv.(Quant (ForAll, [EVar fresh_x_var],
                        Impl(
                          Quant (ForAll, List.map (fun x -> Vars.EVar x) is,
                                 Atom (
                                   Equiv [Term.mk_var fresh_x_var; Term.mk_diff
                                            (Term.mk_name param.h_key)
                                            (Term.mk_name @@ Term.mk_isymb n Message (is))]
                                 )
                                )
                        , equiv)
                       )
                       )
      in
      (axiom_name, enrich, make_conclusion, new_system_e, table)

 with SystemExpr.SystemNotFresh ->
    Tactics.hard_failure
      (Tactics.Failure "System name already defined for another system.")


let declare_system table sdecl =
   match sdecl.Decl.modifier with
     | Rename gf -> global_rename table sdecl gf
     | PRF (ty_vars, hash) -> global_prf table sdecl ty_vars hash
