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
  let old_system, old_single_system = 
    match SE.parse_se table sdecl.Decl.from_sys with
    | Single s as res -> res, s
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
    let vs, subs = Term.refresh_vars `Global evars in
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
  let global_macro_iterator system table ns dec_def data =
    table := Macros.apply_global_data !table ns dec_def old_single_system system data (iterator ());
    ()
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

    let aux_table = ref table in
    Symbols.Macro.iter (global_macro_iterator new_system_expr aux_table) table;
    let table = !aux_table in

      let new_system_e = SystemExpr.pair table old_system_expr new_system_expr in
      let axiom_name = "rename_from_"^(Symbols.to_string old_system_name)
                       ^"_to_"^(Location.unloc sdecl.name) in

      (* we now create the lhs of the obtained conclusion *)
      let fresh_x_var = Vars.make_new Type.Message "mess" in
      let enrich = [Term.mk_var fresh_x_var] in
      let make_conclusion equiv = `Equiv
          Equiv.(Quant (ForAll, [fresh_x_var],
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
  let hash, _ = Theory.convert conv_env [] env hash in
  let is = vars in


  let env = ref env in
  let old_system, old_single_system = match SE.parse_se table sdecl.Decl.from_sys  with
    | Single s as res -> res, s
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
    rw_vars   = Vars.Sv.of_list (fresh_x_var :: is1);
    rw_conds  = [];
    rw_rw     = Term.ESubst (hash_pattern, mk_tryfind);
  }
  in

  let iterator _ t =
    match
      Rewrite.rewrite table old_system (!env) TacticsArgs.(`Once)
        rw_rule (`Reach t)
    with
    | `Result (`Reach res, ls) -> res
    | _ -> t
  in
  let global_macro_iterator system table ns dec_def data =
    table := Macros.apply_global_data !table ns dec_def old_single_system system data (iterator ());
    ()
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
      let aux_table = ref table in
      (*      let new_system_name = Location.mk_loc Location._dummy (Location.unloc sdecl.name) in *)
    Symbols.Macro.iter (global_macro_iterator new_system_expr aux_table) table;
    let table = !aux_table in

      let new_system_e = SystemExpr.pair table old_system_expr new_system_expr in
      let axiom_name = "prf_from_"^(Symbols.to_string old_system_name)
                       ^"_to_"^(Location.unloc sdecl.name)
      in

      (* we now create the lhs of the obtained conclusion *)
      let fresh_x_var = Vars.make_new Type.Message "mess" in
      let enrich = [Term.mk_var fresh_x_var] in
      let make_conclusion equiv = `Equiv
          Equiv.(Quant (ForAll, [fresh_x_var],
                        Impl(
                          Quant (ForAll, is,
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





let global_cca table sdecl ty_vars enc =
  let env,vars = Theory.convert_p_bnds table [] Vars.empty_env ty_vars in
  let conv_env = Theory.{ table; cntxt = InGoal } in
  let enc, _ = Theory.convert conv_env [] env enc in
  let is = vars in


  let env = ref env in
  let old_system, old_single_system = match SE.parse_se table sdecl.Decl.from_sys  with
    | Single s as res -> res, s
    | _ -> assert false
  in

  let cntxt = Constr.{table=table;
                      system= old_system;
                      models=None}
  in

  let enc_fn, enc_key, is_plaintext_name, plaintext, enc_pk, enc_rnd =
    match enc with
    | Term.Fun ((fnenc,eis), _,
                [Term.Name c as m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when (Symbols.is_ftype fnpk Symbols.PublicKey cntxt.table
            && Symbols.is_ftype fnenc Symbols.AEnc table) -> fnenc, sk, true, m, fnpk, r
    | Term.Fun ((fnenc,eis), _,
                [m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when (Symbols.is_ftype fnpk Symbols.PublicKey cntxt.table
            && Symbols.is_ftype fnenc Symbols.AEnc table) -> fnenc, sk, false, m, fnpk, r
    | _ -> Tactics.soft_failure (Tactics.Failure
         "CCA can only be applied on an encryption term enc(t,r,pk(k))")
  in

  let dec_fn =
      begin
        match Symbols.Function.get_data enc_fn table with
        (* we check that the encryption function is used with the associated
           public key *)
        | Symbols.AssociatedFunctions [fndec; fnpk2] when fnpk2 = enc_pk
          ->
          begin
            (* Check syntactic side condition. *)
            let errors =
              Euf.key_ssc ~messages:[enc] ~allow_functions:(fun x -> x = enc_pk)
                ~cntxt fndec enc_key.s_symb
            in
            if errors <> [] then
              Tactics.soft_failure (Tactics.BadSSCDetailed errors);
            fndec
          end

        | _ ->
          Tactics.soft_failure
            (Tactics.Failure
               "The first encryption symbol is not used with the correct \
                public key function.")
      end
  in

  (* TODO: check randomness is used only once, and message is distinct. *)

  (* We first refresh globably the indices to create the left patterns *)
  let is1, left_subst = Term.refresh_vars (`Global) is in
  let mk_left = Term.subst left_subst in
  (* The dec must match all decryption with the corresponding secret key *)
  let fresh_x_var = Vars.make_new Type.Message "x" in
  let dec_pattern = mk_left @@ Term.mk_fun table dec_fn [] [Term.mk_var fresh_x_var;
                                                            Term.mk_name enc_key ] in

  (* Instantiation of the fresh replacement *)
  let ndef = Symbols.{ n_iarr = List.length enc_rnd.s_indices; n_ty = Message ; } in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_CCA") ndef
  in
  let mess_replacement =
    if is_plaintext_name then
        let ns = Term.mk_isymb n Message (enc_rnd.s_indices) in
        Term.mk_name ns
    else
      Term.mk_zeroes (Term.mk_len plaintext) in

  let new_enc =
    Term.mk_fun table enc_fn [] [mess_replacement;
                                 Term.mk_name enc_rnd;
                                 Term.mk_fun table enc_pk [] [Term.mk_name enc_key] ]
  in

  (*
     dec(m,pk(sk(j))) is replaced by
          tryfind i s.t m=new_enc(i) & i =j in plaintext
          else enc(m,r,pk(sk))
 *)
  let tryfind_dec =
    Term.mk_find is Term.(
          (mk_atom `Eq (Term.mk_var fresh_x_var) new_enc)
      ) (plaintext) dec_pattern
  in

  let enc_rw_rule = Rewrite.{
    rw_tyvars = [];
    rw_vars   = Vars.Sv.of_list is;
    rw_conds  = [];
    rw_rw     = Term.ESubst (enc, new_enc);
  }
  in
  let dec_rw_rule = Rewrite.{
    rw_tyvars = [];
    rw_vars   = Vars.Sv.of_list (fresh_x_var :: is1);
    rw_conds  = [];
    rw_rw     = Term.ESubst (dec_pattern, tryfind_dec);
  }
  in

  let iterator cenv t =
    match
      Rewrite.rewrite table old_system (!env) TacticsArgs.(`Once)
        enc_rw_rule (`Reach t)
    with
    | `Result (`Reach res, ls) ->
      begin
        match
          Rewrite.rewrite table old_system (!env) TacticsArgs.(`Once)
            dec_rw_rule (`Reach res)
        with
        | `Result (`Reach res2, ls) -> res2
        | _ -> res
      end
    | _ ->
      begin
        match
          Rewrite.rewrite table old_system (!env) TacticsArgs.(`Once)
            dec_rw_rule (`Reach t)
        with
        | `Result (`Reach res2, ls) -> res2
        | _ -> t
      end
  in
  let global_macro_iterator system table ns dec_def data =
    table := Macros.apply_global_data !table ns dec_def old_single_system system data (iterator ());
    ()
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

    let aux_table = ref table in
    Symbols.Macro.iter (global_macro_iterator new_system_expr aux_table) table;
    let table = !aux_table in


    let new_system_e = SystemExpr.pair table old_system_expr new_system_expr in
    let axiom_name = "cca_from_"^(Symbols.to_string old_system_name)
                       ^"_to_"^(Location.unloc sdecl.name)
    in

    (* we now create the lhs of the obtained conclusion *)
    let fresh_x_var = Vars.make_new Type.Message "mess" in
    let rdef = Symbols.{ n_iarr = List.length is; n_ty = Message ; } in
    let table,r =
      Symbols.Name.declare table (L.mk_loc L._dummy "r_CCA") rdef
    in

    let enrich = [Term.mk_var fresh_x_var] in
    let make_conclusion equiv = `Equiv
        Equiv.(Quant (ForAll, [fresh_x_var],
                      Impl(
                        Quant (ForAll, is,
                               Atom (
                                 Equiv [Term.mk_var fresh_x_var;
                                        Term.mk_diff
                                          (Term.mk_name enc_key)
                                          (Term.mk_name @@ Term.mk_isymb n Message (is));
                                        Term.mk_diff
                                          (Term.mk_name enc_rnd)
                                          (Term.mk_name @@ Term.mk_isymb r Message (is))
                                       ]
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
     | CCA (ty_vars, enc) -> global_cca table sdecl ty_vars enc
