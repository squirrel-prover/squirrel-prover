open Utils

module SE   = SystemExpr
module L    = Location

(*------------------------------------------------------------------*)
(** rewrite a rule as much as possible without recursing *)
let rewrite_norec
    (table  : Symbols.table)
    (system : SE.t)
    (venv   : Vars.env)
    (rule   : Rewrite.rw_erule) 
    (t      : Term.term)
  : Term.term 
  =
  assert (rule.rw_conds = []);
  let Term.ESubst (left,right) = rule.rw_rw in
  let pat : Term.term Match.pat = Match.{ 
      pat_tyvars = rule.rw_tyvars; 
      pat_vars   = rule.rw_vars; 
      pat_term   = left;
    } 
  in
  let rw_inst : Match.Pos.f_map = 
    fun occ vars _conds _p ->
      match Match.T.try_match table system occ pat with
      | NoMatch _ | FreeTyv -> `Continue

      (* head matches *)
      | Match mv ->
        let subst = Match.Mvar.to_subst ~mode:`Match mv in
        let left = Term.subst subst left in
        let right = Term.subst subst right in
        assert (left = occ);
        `Map right
  in
  let _, f = Match.Pos.map ~m_rec:false rw_inst venv t in
  f

(*------------------------------------------------------------------*)
let parse_single_system_name table sdecl : SE.fset * System.Single.t =
  let res = SE.parse table sdecl.Decl.from_sys in
  match SE.(to_list (to_fset res)) with
  | [_,s] -> SE.to_fset res, s
  | _ ->
    Tactics.soft_failure ~loc:(L.loc sdecl.Decl.from_sys)
      (Failure "a single system must be provided")

(*------------------------------------------------------------------*)
(** Convertion of system modifiers arguments.
    - [bnds] are additional binded variables. *)
let conv_term table system ~bnds (term : Theory.term)
  : Vars.env * Vars.vars * Term.term
  =
  let env = Env.init ~table ~system:system () in
  let env,is = Theory.convert_p_bnds env bnds in

  Vars.check_type_vars is [Type.Index]
    (fun () ->
       let loc =
         let hloc = L.loc @@ snd @@ List.hd   bnds in
         let eloc = L.loc @@ snd @@ List.last bnds in
         L.merge hloc eloc
       in
       Tactics.hard_failure ~loc
         (Tactics.Failure "Only index variables can be bound."));

  let conv_env = Theory.{ env; cntxt = InGoal } in
  let t, _ = Theory.convert conv_env term in
  env.vars, is, t

(*------------------------------------------------------------------*)
(** Return type for [global_*] functions below. *)
type ret_t =
  string *
  Term.term list *
  (Equiv.global_form -> Equiv.any_form) *
  SystemExpr.pair *
  Symbols.table

(*------------------------------------------------------------------*)
(** {2 Renaming} *)

let global_rename table sdecl (gf : Theory.global_formula) : ret_t =

  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  (* Convert equivalence formula [gf].
     We parse it with old_single_system on both sides,
     but any system would work here since the equivalence must
     relate names. *)
  let system =
    SE.update
      ~pair:(SE.make_pair old_single_system old_single_system)
      SE.context_any
  in
  let env = Env.init ~table ~system () in
  let conv_env = Theory.{ env; cntxt = InGoal } in
  let f = Theory.convert_global_formula conv_env gf in

  (* Decompose it as universally quantified equivalence over names. *)
  let vs, f = Equiv.Smart.decompose_forall f in
  Vars.check_type_vars vs [Type.Index]
    (fun () -> Tactics.hard_failure ~loc:(L.loc gf)
        (Tactics.Failure "Only index variables can be bound."));
  let ns1, ns2, n1, n2 =
    match f with
    |  Atom
         (Equiv ([Term.Diff (Explicit [_,Term.Name ns1; _,Term.Name ns2])]))
      ->
      ns1, ns2, Term.mk_name ns1, Term.mk_name ns2

    | _ ->
      Tactics.hard_failure ~loc:(L.loc gf) (Failure "arguments ill-formed")
  in

  (* We check that n2 does not occur in the old system using fresh. *)
  let cntxt =
    Constr.make_context ~table ~system:(SE.singleton old_single_system)
  in
  let iter = new Fresh.find_name ~cntxt true ns2.s_symb in
  let () =
    try
      SystemExpr.iter_descrs
        table (SE.singleton old_single_system)
        (fun action_descr ->
           iter#visit_message (snd action_descr.output) ;
           iter#visit_message (snd action_descr.condition) ;
           List.iter (fun (_,m) -> iter#visit_message m) action_descr.updates)
    with Fresh.Name_found ->
      Tactics.hard_failure
        (Tactics.Failure "The name on the right-hand side already \
                          occurs in the left-hand side.")
  in

  (* We now build the rewrite rule *)
  let evars = Term.get_vars n1 in
  let vs, subs = Term.refresh_vars `Global evars in
  let n1', n2' = (Term.subst subs n1, Term.subst subs n2) in
  let rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_vars = Vars.Sv.of_list vs;
      rw_conds = [];
      rw_rw = Term.ESubst (n1', n2');
    }
  in
  let map cenv t : Term.term =
    rewrite_norec table (old_system:>SE.t) env.vars rw_rule t
  in
  let global_macro_iterator system table ns dec_def _ : unit =
    table :=
      Macros.update_global_data
        !table ns dec_def
        old_single_system system (map ())
  in

  (* We now declare the system. *)
  let table, new_system =
    SystemExpr.clone_system
      table (SE.singleton old_single_system)
      sdecl.name (Action.descr_map map)
  in
  let new_single_system =
    match System.projections table new_system with
      | [p] -> System.Single.make table new_system p
      | _ -> assert false
  in
  let aux_table = ref table in
  Symbols.Macro.iter (global_macro_iterator new_single_system aux_table) table;
  let table = !aux_table in

  (* We finally put as axiom the equivalence between the old and the
     new system. *)
  let old_new_pair =
    SE.make_pair old_single_system new_single_system
  in
  let axiom_name =
    let old_system_name = Symbols.to_string old_single_system.system in
    "rename_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in

  let make_conclusion equiv =
    let fimpl =
      Equiv.Impl(
        Equiv.mk_forall evars
          (Atom (Equiv [Term.mk_var fresh_x_var;
                        Term.mk_diff ["left",n1;"right",n2]])),
        equiv)
    in
    `Equiv (Equiv.mk_forall [fresh_x_var] fimpl)
  in
  (axiom_name, enrich, make_conclusion, old_new_pair, table)


(*------------------------------------------------------------------*)
(** {2 PRF} *)

let global_prf table sdecl bnds hash : ret_t =

  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let venv, is, hash =
    let context =
      SystemExpr.update
        ~set:(SE.singleton old_single_system)
        SystemExpr.context_any
    in
    conv_term table context ~bnds hash
  in

  let cntxt =
    Constr.make_context ~table ~system:(SE.singleton old_single_system)
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

  let map _ t =
    rewrite_norec table (old_system:>SE.t) venv rw_rule t
  in
  let global_macro_iterator system table ns dec_def _ : unit =
    table :=
      Macros.update_global_data
        !table ns
        dec_def old_single_system system (map ())
  in

  (* We now declare the system. *)
  let table, new_system =
    SystemExpr.clone_system
      table (SE.singleton old_single_system)
      sdecl.Decl.name (Action.descr_map map)
  in
  let new_single_system =
    match System.projections table new_system with
      | [p] -> System.Single.make table new_system p
      | _ -> assert false
  in
  let aux_table = ref table in
  Symbols.Macro.iter (global_macro_iterator new_single_system aux_table) table;
  let table = !aux_table in

  (* We finally put as axiom the equivalence between the old
     and the new system. *)
  let old_new_pair =
    SE.make_pair old_single_system new_single_system
  in
  let axiom_name =
    let old_system_name = Symbols.to_string old_single_system.system in
    "prf_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [Term.mk_var fresh_x_var;
               Term.mk_diff
                 ["left", Term.mk_name param.h_key;
                  "right", Term.mk_name @@ Term.mk_isymb n Message (is)]])
    in
    let concl = 
      Equiv.mk_forall [fresh_x_var]
        (Equiv.Smart.mk_impl ~simpl:false (Equiv.mk_forall is atom) equiv)
    in
    `Equiv concl
  in
  (axiom_name, enrich, make_conclusion, old_new_pair, table)


(*------------------------------------------------------------------*)
(** {2 CCA} *)

  
let global_cca table sdecl bnds (p_enc : Theory.term) : ret_t =

  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let venv, is, enc =
    let context =
      SystemExpr.update
        ~set:(SE.singleton old_single_system)
        SystemExpr.context_any
    in
    conv_term table context ~bnds p_enc
  in

  let cntxt =
    Constr.make_context ~table ~system:(SE.singleton old_single_system)
  in

  let enc_fn, enc_key, plaintext, enc_pk, enc_rnd =
    match enc with
    | Term.Fun ((fnenc,eis), _,
                [m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when Symbols.is_ftype fnpk Symbols.PublicKey cntxt.table &&
           Symbols.is_ftype fnenc Symbols.AEnc table ->
      fnenc, sk, m, fnpk, r

    | _ ->
      Tactics.soft_failure ~loc:(L.loc p_enc)
        (Tactics.Failure
           "CCA can only be applied on an encryption term enc(t,r,pk(k))")
  in

  let dec_fn =
    match Symbols.Function.get_data enc_fn table with
    (* we check that the encryption function is used with the associated
       public key *)
    | Symbols.AssociatedFunctions [fndec; fnpk2] when fnpk2 = enc_pk ->
      (* Check syntactic side condition. *)
      let errors =
        Euf.key_ssc ~messages:[enc] ~allow_functions:(fun x -> x = enc_pk)
          ~cntxt fndec enc_key.s_symb
      in
      
      if errors <> [] then
        Tactics.soft_failure (Tactics.BadSSCDetailed errors);
      
      fndec

    | _ ->
      Tactics.soft_failure
        (Tactics.Failure
           "The first encryption symbol is not used with the correct \
            public key function.")
  in

  (* TODO: check randomness is used only once, and message is distinct. *)

  (* We first refresh globably the indices to create the left patterns *)
  let is1, left_subst = Term.refresh_vars (`Global) is in

  (* The dec must match all decryption with the corresponding secret key *)
  let fresh_x_var = Vars.make_new Type.Message "x" in
  let dec_pattern =
    Term.mk_fun table dec_fn [] [ Term.mk_var fresh_x_var;
                                  Term.mk_name enc_key ]
  in
  let dec_pattern = Term.subst left_subst dec_pattern in

  (* Instantiation of the fresh replacement *)
  let ndef = Symbols.{
      n_iarr = List.length enc_rnd.s_indices;
      n_ty = Message; }
  in
  let table,n =
    Symbols.Name.declare cntxt.table (L.mk_loc L._dummy "n_CCA") ndef
  in
  let mess_replacement =
    if Term.is_name plaintext then
      let ns = Term.mk_isymb n Message (enc_rnd.s_indices) in
      Term.mk_name ns
    else
      Term.mk_zeroes (Term.mk_len plaintext) in

  let new_enc =
    let t_pk = Term.mk_fun table enc_pk [] [Term.mk_name enc_key]  in
    Term.mk_fun table enc_fn [] [ mess_replacement;
                                  Term.mk_name enc_rnd;
                                  t_pk ]
  in

  (* We replace
       dec(m,pk(sk(j))) 
     by:
       tryfind i s.t m=new_enc(i) & i =j 
               else enc(m,r,pk(sk)) 
     in plaintext *)
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

  let map cenv t =
    rewrite_norec table (old_system:>SE.t) venv enc_rw_rule t |>
    rewrite_norec table (old_system:>SE.t) venv dec_rw_rule
  in
  let global_macro_iterator system table ns dec_def _ =
    table :=
      Macros.update_global_data
        !table ns
        dec_def old_single_system system (map ())
  in

  let table, new_system =
    SystemExpr.clone_system
      table (SE.singleton old_single_system)
      sdecl.Decl.name (Action.descr_map map)
  in
  let new_single_system =
    match System.projections table new_system with
      | [p] -> System.Single.make table new_system p
      | _ -> assert false
  in
  let aux_table = ref table in
  Symbols.Macro.iter (global_macro_iterator new_single_system aux_table) table;
  let table = !aux_table in

  (* We finally put as axiom the equivalence between the old and
     the new system. *)
  let old_new_pair =
    SE.make_pair old_single_system new_single_system
  in
  let axiom_name =
    let old_system_name = Symbols.to_string old_single_system.system in
    "cca_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let rdef = Symbols.{ n_iarr = List.length is; n_ty = Message ; } in
  let table,r =
    Symbols.Name.declare table (L.mk_loc L._dummy "r_CCA") rdef
  in

  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [ Term.mk_var fresh_x_var;
                
                Term.mk_diff
                  ["left", Term.mk_name enc_key;
                   "right", Term.mk_name @@ Term.mk_isymb n Message is];
                
               Term.mk_diff
                 ["left", Term.mk_name enc_rnd;
                  "right", Term.mk_name @@ Term.mk_isymb r Message is] ])
    in
    let concl = Equiv.Impl (Equiv.mk_forall is atom, equiv) in      
    `Equiv (Equiv.mk_forall [fresh_x_var] concl)
  in
  (axiom_name, enrich, make_conclusion, old_new_pair, table)


(*------------------------------------------------------------------*)
let declare_system table sdecl =
  match sdecl.Decl.modifier with
  | Rename gf        -> global_rename table sdecl        gf
  | PRF (bnds, hash) -> global_prf    table sdecl bnds hash
  | CCA (bnds, enc)  -> global_cca    table sdecl bnds  enc
