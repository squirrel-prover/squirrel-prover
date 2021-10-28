open Utils

module SE   = SystemExpr


let global_rename table sdecl gf =
  let env,vars = Theory.convert_p_bnds table [] Vars.empty_env [] in
  let conv_env = Theory.{ table; cntxt = InGoal } in
  let f = Theory.convert_global_formula conv_env [] env gf in
  let ns1, ns2, n1, n2 =
    match f with
    | Quant (ForAll, is, Atom (Equiv ([
        Term.Diff (Term.Name ns1, Term.Name ns2)
      ]
      )) ) ->  ns1, ns2, Term.mk_name ns1, Term.mk_name ns2

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


let declare_system table sdecl =
   match sdecl.Decl.modifier with
    | Rename gf -> global_rename table sdecl gf
    | _ -> assert false
