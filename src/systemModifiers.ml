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

    let iterator t =
      match
        Rewrite.rewrite table old_system env TacticsArgs.(`Any)
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
                       ^"_to_"^(Location.unloc sdecl.name)
      in
      (axiom_name, new_system_e, table)
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


  (* let is1, left_subst = Term.refresh_vars (`InEnv env) is in
   * let left_hash = Term.subst left_subst hash in *)

  let is2, subst = Term.refresh_vars (`InEnv env) is in
  let fresh_mess = Term.subst subst param.h_cnt in
  let fresh_key = Term.subst subst (Term.mk_name param.h_key) in
  let fresh_key_ids = match fresh_key with
    | Term.Name s -> s.s_indices
    | _ -> assert false
  in

  (* We will now instantiate the new system. *)

  (* Instantiation of the fresh name *)
  let ndef = Symbols.{ n_iarr = List.length is; n_ty = Message ; } in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_PRF") ndef
  in
  (* the hash h of a message m will be replaced by tryfind is s.t = fresh mess
     in fresh else h *)
  let mk_tryfind nhash =
    match nhash with
    | Term.Fun ((h_fn, _), _, [h_cnt; Name s]) when s.s_symb = param.h_key.s_symb ->
        let ns = Term.mk_isymb n Message (is2) in
        Term.mk_find is2 Term.(
            mk_and
              (mk_atom `Eq h_cnt fresh_mess)
              (mk_indices_eq fresh_key_ids s.s_indices)
          ) (Term.mk_name ns) nhash
    | _ -> Printer.pr "%a" Term.pp nhash;  assert false
  in
  let rw_rule = Rewrite.{
    rw_tyvars = [];
    rw_vars = Vars.Sv.of_list (List.map Vars.evar is);
    rw_conds = [];
    rw_rw = Term.ESubst (hash, mk_tryfind hash);
  }
  in
  let iterator t =
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
      let axiom_name = "rename_from_"^(Symbols.to_string old_system_name)
                       ^"_to_"^(Location.unloc sdecl.name)
      in
      (axiom_name, new_system_e, table)

 with SystemExpr.SystemNotFresh ->
    Tactics.hard_failure
      (Tactics.Failure "System name already defined for another system.")


let declare_system table sdecl =
   match sdecl.Decl.modifier with
     | Rename gf -> global_rename table sdecl gf
     | PRF (ty_vars, hash) -> global_prf table sdecl ty_vars hash
