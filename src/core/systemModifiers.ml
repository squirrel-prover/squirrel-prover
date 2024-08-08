open Utils

module Name = Occurrences.Name
                
module SE = SystemExpr
module L  = Location

module Pos = Match.Pos
               
module Sv = Vars.Sv
module Sp = Pos.Sp

module Args = TacticsArgs
module TS   = TraceSequent
module LT   = LowTactics
module TLT  = LT.TraceLT

(*------------------------------------------------------------------*)
let soft_failure = Tactics.soft_failure

(*------------------------------------------------------------------*)
(** Simple case of [rewrite], without recursion and with a single rewriting 
    rule. Rewriting can fail (hence [strict=false]). *)
let high_rewrite_norec
    (table  : Symbols.table)
    (system : SE.t)
    (rule   : Rewrite.rw_rule) 
    (t      : Term.term)
  : Term.term 
  =
  let mk_rule = fun _ _ -> Some rule in

  let env = Vars.empty_env in
  (* only local variables, hence [env] should is useless here. *)
  
  Rewrite.high_rewrite ~mode:(`TopDown false) ~strict:false table Params.empty env system mk_rule t
    

(*------------------------------------------------------------------*)
type system_map_arg = Macros.system_map_arg


(*------------------------------------------------------------------*)
(** Low-level system cloning function.
    [clone_system table old new f] registers a new system [new],
    obtained by modifying the actions of [old] with [f].
    Returns the updated table and system symbol.
    Does not clone global macros. *)
let clone_system 
    (table      : Symbols.table)
    (old_system : SE.fset)
    (new_system : Symbols.lsymb)
    (map        : Action.descr -> Action.descr)
  : Symbols.table * Symbols.system 
  =
  let projections = List.map fst (SE.to_list old_system) in
  let old_actions = SE.descrs table old_system in
  let table, new_system = System.declare_empty table new_system projections in
  let table =
    System.Msh.fold
      (fun _ descr table ->
         let descr = map descr in
         let table,_,_ = System.register_action table new_system descr in
         table)
      old_actions
      table
  in

  let table = Lemma.add_depends_mutex_lemmas table new_system in

  table, new_system

(*------------------------------------------------------------------*)
(** High-level system cloning function. *)
let clone_system_map
    (table    : Symbols.table)
    (system   : System.Single.t)
    (new_name : Symbols.lsymb)
    (fmap     :
       ( system_map_arg ->
         Symbols.macro ->
         Term.term ->
         Term.term ))
  : Symbols.table * SE.pair 
  =
  (* We declare the system *)
  let table, new_system =
    clone_system
      table (SE.singleton system) new_name
      (fun descr -> 
         let _, s  = Term.refresh_vars descr.indices in
         let descr = Action.subst_descr s descr in

         Action.descr_map (fun _ -> fmap (ADescr descr)) descr)
  in

  let new_single_system =
    match System.projections table new_system with
      | [p] -> System.Single.make table new_system p
      | _ -> assert false
  in

  let old_new_pair =
    SE.make_pair
      (Projection.left, system)
      (Projection.right, new_single_system)
  in

  let global_macro_fold
      (ns : Symbols.macro) _ (table : Symbols.table) : Symbols.table
    =
    Macros.update_global_data table ns system new_single_system fmap
  in

  let table = Symbols.Macro.fold global_macro_fold table table in

  table, old_new_pair

(*------------------------------------------------------------------*)
let parse_single_system_name table sdecl : SE.fset * System.Single.t =
  let _, res = SE.Parse.parse ~implicit:false ~se_env:[] table sdecl.Decl.from_sys in
  match SE.(to_list (to_fset res)) with
  | [_,s] -> SE.to_fset res, s
  | _ ->
    let loc = match sdecl.Decl.from_sys with se -> L.loc se in
    soft_failure ~loc (Failure "a single system must be provided")

(*------------------------------------------------------------------*)
(** Convertion of system modifiers arguments.
    - [bnds] are additional binded variables. *)
let conv_term ?pat table system ~bnds (term : Typing.term)
  : Vars.vars * Term.term
  =
  let env = Env.init ~table ~system:system () in
  let env,is = Typing.convert_bnds ~mode:NoTags env bnds in

  Vars.check_type_vars is [Type.tindex]
    (fun () ->
       let loc =
         let hloc = L.loc @@ snd @@ List.hd   bnds in
         let eloc = L.loc @@ snd @@ List.last bnds in
         L.merge hloc eloc
       in
       Tactics.hard_failure ~loc
         (Tactics.Failure "Only index variables can be bound."));

  let conv_env = Typing.{ env; cntxt = InGoal } in
  let t, _ = Typing.convert ?pat conv_env term in
  is, t

(*------------------------------------------------------------------*)
let mk_equiv_statement
    table 
    new_axiom_name enrich make_conclusion new_system
  : Goal.statement
  =
  let context = SE.{ set = new_system; pair = Some (SE.to_pair new_system) ; } in
  let formula =
    fst (Goal.make_obs_equiv ~enrich table context)
    |> Equiv.any_statement_to_equiv
  in
  let formula = make_conclusion formula in
  Goal.{ name    = new_axiom_name; 
         params  = Params.empty;
         system  = context; 
         formula }


(*------------------------------------------------------------------*)
(** {2 Renaming} *)

let global_rename
    (table : Symbols.table) 
    sdecl (gf : Typing.global_formula)
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  (* Convert equivalence formula [gf].
     We parse it with old_single_system on both sides,
     but any system would work here since the equivalence must
     relate names. *)
  let system =
    let pair =
      (SE.make_pair
         (Projection.left, old_single_system)
         (Projection.right, old_single_system))
    in
    SE.{ set = (pair :> SE.t); pair = Some pair ; } 
  in
  let env = Env.init ~table ~system () in
  let conv_env = Typing.{ env; cntxt = InGoal } in
  let f = Typing.convert_global_formula conv_env gf in

  (* Decompose it as universally quantified equivalence over names. *)
  let vs, f = Equiv.Smart.decompose_forall f in
  Vars.check_type_vars vs [Type.tindex]
    (fun () -> Tactics.hard_failure ~loc:(L.loc gf)
        (Tactics.Failure "Only index variables can be bound."));
  let _ns1, ns2, n1, n2 =
    match f with
    |  Atom
        (Equiv ({terms = [Term.Diff (Explicit [_,(Term.Name _ as ns1);
                                      _, (Term.Name _ as ns2)])]; bound = None}))
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
      ->
      Name.of_term ns1, Name.of_term ns2, ns1, ns2

    | _ ->
      Tactics.hard_failure ~loc:(L.loc gf) (Failure "arguments ill-formed")
  in

  (* We check that n2 does not occur in the old system using fresh. *)
  let cntxt =
    Constr.make_context ~table ~system:(SE.singleton old_single_system)
  in
  let iter = new OldFresh.deprecated_find_name ~cntxt true ns2.symb.s_symb in
  let () =
    try
      SystemExpr.iter_descrs
        table (SE.singleton old_single_system)
        (fun action_descr ->
           iter#visit_message (snd action_descr.output) ;
           iter#visit_message (snd action_descr.condition) ;
           List.iter (fun (_,args,m) ->
               List.iter iter#visit_message (m :: args)
             ) action_descr.updates)
    with OldFresh.Deprecated_Name_found ->
      Tactics.hard_failure
        (Tactics.Failure "The name on the right-hand side already \
                          occurs in the left-hand side.")
  in

  (* We now build the rewrite rule *)
  let evars = Term.get_vars n1 in
  let vs, subs = Term.refresh_vars evars in
  let n1', n2' = (Term.subst subs n1, Term.subst subs n2) in

  let rw_vars = (* remove variable that do not need to be inferred from [vs] *)
    let fv = Term.fv n1' in
    List.filter (fun v -> Sv.mem v fv) vs
  in

  let v = SE.Var.of_ident (Ident.create "'P") in
  let rw_rule = Rewrite.{
      rw_params = { Params.empty with se_vars = [v,[]]; };
      rw_system = SE.var v;
      rw_vars   = Vars.Tag.local_vars rw_vars;
      rw_conds  = [];
      rw_rw     = n1', n2';
      rw_kind   = GlobalEq;
      rw_bound = Glob;
    }
  in

  let fmap _ _ms t : Term.term =
    high_rewrite_norec table (old_system :> SE.t) rw_rule t
  in
  
  let table, old_new_pair =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    let old_system_name = Symbols.path_to_string old_single_system.system in
    "rename_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_fresh Type.tmessage "mess" in
  let enrich = [Term.mk_var fresh_x_var] in

  let make_conclusion equiv =
    let fimpl =
      Equiv.Impl(
        Equiv.Smart.mk_forall_tagged
          (Vars.Tag.global_vars ~const:true evars)
          (* FIXME: unclear what tags should be used here *)
          (Atom (Equiv {terms = [Term.mk_var fresh_x_var;
                        Term.mk_diff [Projection.left,n1;Projection.right,n2]]; bound = None})),
        equiv)
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
    in
    Equiv.GlobalS (Equiv.Smart.mk_forall [fresh_x_var] fimpl)
  in
  let lemma =
    mk_equiv_statement
      table
      axiom_name enrich make_conclusion (old_new_pair :> SE.t)
  in
  (Some lemma, [], table)



(*------------------------------------------------------------------*)
(* Timeless global tactis can only be applied to simple terms. that
   are only basic function applications over names. *)
let rec is_simple (t : Term.term) : bool =
  let are_simple = List.for_all is_simple in
  match t with
  | Var _
  | Fun (_, _)  -> true
    
  | App (t, l) -> are_simple (t :: l)

  | Tuple l                       
  | Name (_,l) -> are_simple l 

  | Term.Int    _
  | Term.String _
  | Let _
  | Macro (_, _, _) 
  | Action (_,_) 
  | Proj (_, _) 
  | Diff (_) 
  | Find (_, _, _, _)
  | Quant (_, _, _) -> false

(*------------------------------------------------------------------*)
(** {2 PRF} *)

let global_prf
    (table : Symbols.table)
    (sdecl : Decl.system_modifier)
    (bnds  : Typing.bnds)
    (hash  : Typing.term)
  : Goal.statement option * Goal.t list * Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let is, hash =
    let context = SE.(reachability_context (singleton old_single_system)) in
    conv_term table context ~bnds hash
  in

  let cntxt =
    Constr.make_context ~table ~system:(SE.singleton old_single_system)
  in

  let (h_fn, h_cnt, h_key) =
    match hash with
    | Term.App (Fun (h_fn, applied_fty), [Tuple [h_cnt; Name (key, key_args)]]) ->
      (* crypto function cannot use polymorphism *)
      assert (applied_fty.ty_args = []);
      (h_fn, h_cnt, Name.{ symb = key; args = key_args; })      
    | _ -> Tactics.soft_failure Tactics.Bad_SSC
  in

  (* Check syntactic side condition. *)
  let errors =
    OldEuf.key_ssc ~globals:true
      ~elems:{terms = []; bound = None} ~allow_functions:(fun _ -> false)
  (*TODO:Concrete : Probably something to do to create a bounded goal*)
      ~cntxt h_fn h_key.symb.s_symb
  in
  if errors <> [] then
    soft_failure (Tactics.BadSSCDetailed errors);

  (* Check that the target hash is a simple term (no macros, no diff, no quant) *)
  if not (is_simple hash) then
    Tactics.hard_failure 
      (Failure
         "the target term should be a simple term, without macros, diff, quantifications, etc.");
  
  (* We first refresh globably the indices to create the left pattern *)
  let is1, left_subst = Term.refresh_vars is in

  let left_key =  Term.subst left_subst (Name.to_term h_key) in
  let left_key_ids =
    match left_key with
    | Term.Name (_,ids) -> ids
    | _ -> assert false
  in
  (* We create the pattern for the hash *)
  let fresh_x_var = Vars.make_fresh Type.tmessage "x" in
  let hash_pattern =
    Term.mk_fun_tuple table h_fn [Term.mk_var fresh_x_var; left_key ]
  in

  (* Instantiation of the fresh name *)
  let ty_args = List.map Vars.ty is in
  let n_fty = Type.mk_ftype_tuple [] ty_args Type.tmessage in
  let ndef = Symbols.Name { n_fty } in
  let s = (L.mk_loc L._dummy "n_PRF") in
  let table,n = Symbols.Name.declare ~approx:true table s ~data:ndef in
  let table = Process.add_namelength_axiom table n n_fty in
  
  (* the hash h of a message m will be replaced by tryfind is s.t = fresh mess
     in fresh else h *)
  let mk_tryfind =
    let ns = Term.mk_symb n Type.tmessage in
    Term.mk_find is Term.(
        mk_and
          (mk_atom `Eq (Term.mk_var fresh_x_var) h_cnt)
          (mk_eqs ~simpl_tuples:true left_key_ids h_key.args)
      ) (Term.mk_name_with_tuple_args ns (Term.mk_vars is)) hash_pattern
  in

  let rw_vars = (* remove variable that do not need to be inferred from [is1] *)
    let fv = Term.fv hash_pattern in
    List.filter (fun v -> Sv.mem v fv) is1
  in

  let v = SE.Var.of_ident (Ident.create "'P") in
  let rw_rule = Rewrite.{
      rw_params = { Params.empty with se_vars = [v,[]]; };
      rw_system = SE.var v;
      rw_vars   = Vars.Tag.local_vars (fresh_x_var :: rw_vars);
      rw_conds  = [];
      rw_rw     = hash_pattern, mk_tryfind;
      rw_kind   = GlobalEq;
      rw_bound = Glob;
    }
  in

  let fmap _ _ms t =
    high_rewrite_norec table (old_system :> SE.t) rw_rule t
  in

  let table, old_new_pair =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    let old_system_name = Symbols.path_to_string old_single_system.system in
    "prf_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_fresh Type.tmessage "mess" in
  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv {terms = [Term.mk_var fresh_x_var;
               Term.mk_diff
                 [Projection.left, Name.to_term h_key;
                  Projection.right,
                  Term.mk_name_with_tuple_args
                    (Term.mk_symb n Type.tmessage) (Term.mk_vars is)]]; bound = None})
        (*TODO:Concrete: Probably something to bound to create a bounded goal*)
    in
    let concl = 
      Equiv.Smart.mk_forall [fresh_x_var]
        (Equiv.Smart.mk_impl ~simpl:false
           (Equiv.Smart.mk_forall_tagged
              (* FIXME: unclear what tags should be used here *)
              (Vars.Tag.global_vars ~const:true is) atom)
           equiv)
    in
    Equiv.GlobalS concl
  in

  let lemma =
    mk_equiv_statement
      table
      axiom_name enrich make_conclusion (old_new_pair :> SE.t)
  in

  Some lemma, [], table



(*------------------------------------------------------------------*)
(** {2 CCA} *)

  
let global_cca
    (table : Symbols.table) 
    sdecl bnds (p_enc : Typing.term)
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let is, enc =
    let context = SE.(reachability_context (singleton old_single_system)) in
    conv_term table context ~bnds p_enc
  in

  let cntxt =
    Constr.make_context ~table ~system:(SE.singleton old_single_system)
  in

  let enc_fn, (enc_key : Name.t), plaintext, enc_pk, (enc_rnd : Name.t) =
    match enc with
    | Term.App (Fun (fnenc, _),
                [Tuple [m; Term.Name _ as r;
                        Term.App (Fun (fnpk, _), [Term.Name _ as sk])]])
      when Symbols.OpData.(is_abstract_with_ftype fnpk  PublicKey table) &&
           Symbols.OpData.(is_abstract_with_ftype fnenc AEnc      table) ->
      fnenc, Name.of_term sk, m, fnpk, Name.of_term r

    | _ ->
      soft_failure ~loc:(L.loc p_enc)
        (Tactics.Failure
           "CCA can only be applied on an encryption term enc(t,r,pk(k))")
  in

  let dec_fn =
    match Symbols.OpData.get_abstract_data enc_fn table with
    (* we check that the encryption function is used with the associated
       public key *)
    | _, [fndec; fnpk2] when fnpk2 = enc_pk ->
      (* Check syntactic side condition. *)
      let errors =
        OldEuf.key_ssc ~globals:true
          ~messages:[enc] ~allow_functions:(fun x -> x = enc_pk)
          ~cntxt fndec enc_key.symb.s_symb
      in
      
      if errors <> [] then
        soft_failure (Tactics.BadSSCDetailed errors);
      
      fndec

    | _ ->
      soft_failure
        (Tactics.Failure
           "The first encryption symbol is not used with the correct \
            public key function.")
  in
  (* Check that the target enc is a simple term (no macros, no diff, no quant) *)
  if not (is_simple enc) then
    Tactics.hard_failure 
      (Failure
         "the target term should be a simple term, without macros, diff, quantifications, etc.");

  
  (* TODO: check randomness is used only once, and message is distinct. *)

  (* We first refresh globably the indices to create the left patterns *)
  let is1, left_subst = Term.refresh_vars is in

  (* The dec must match all decryption with the corresponding secret key *)
  let fresh_x_var = Vars.make_fresh Type.tmessage "x" in
  let dec_pattern =
    Term.mk_fun_tuple table dec_fn [ Term.mk_var fresh_x_var;
                                     Name.to_term enc_key ]
  in
  let dec_pattern = Term.subst left_subst dec_pattern in

  (* Instantiation of the fresh replacement *)
  let ty_args = List.map Term.ty enc_rnd.args in
  let n_fty = Type.mk_ftype_tuple [] ty_args Type.tmessage in
  let ndef = Symbols.Name { n_fty } in
  let s = L.mk_loc L._dummy "n_CCA" in
  let table,n = Symbols.Name.declare ~approx:true table s ~data:ndef in
  let table = Process.add_namelength_axiom table n n_fty in
  
  let mess_replacement =
    if Term.is_name plaintext then
      let ns = Term.mk_symb n Type.tmessage in
      Term.mk_name_with_tuple_args ns enc_rnd.args
    else
      Library.Prelude.mk_zeroes table (Term.mk_len plaintext) in

  let new_enc =
    let t_pk = Term.mk_fun table enc_pk [Name.to_term enc_key]  in
    Term.mk_fun_tuple table enc_fn [ mess_replacement;
                                     Name.to_term enc_rnd;
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

  let enc_rw_rule = 
    let enc_rw_vars = (* remove variable that do not need to be inferred from [is] *)
      let fv = Term.fv enc in
      List.filter (fun v -> Sv.mem v fv) is
    in
    let v = SE.Var.of_ident (Ident.create "'P") in
    Rewrite.{
      rw_params = { Params.empty with se_vars = [v,[]]; };
      rw_system = SE.var v;
      rw_vars   = Vars.Tag.local_vars enc_rw_vars;
      rw_conds  = [];
      rw_rw     = enc, new_enc;
      rw_kind   = GlobalEq;
      rw_bound = Glob;
    }
  in
  let dec_rw_rule =
    let dec_rw_vars = (* remove variable that do not need to be inferred from [is] *)
      let fv = Term.fv dec_pattern in
      List.filter (fun v -> Sv.mem v fv) is1
    in
    let v = SE.Var.of_ident (Ident.create "'P") in
    Rewrite.{
      rw_params = { Params.empty with se_vars = [v,[]]; };
      rw_system = SE.var v;
      rw_vars   = Vars.Tag.local_vars (fresh_x_var :: dec_rw_vars);
      rw_conds  = [];
      rw_rw     = dec_pattern, tryfind_dec;
      rw_kind   = GlobalEq;
      rw_bound = Glob;
    }
  in

  let fmap _ _ms t =
    high_rewrite_norec table (old_system :> SE.t) enc_rw_rule t |>
    high_rewrite_norec table (old_system :> SE.t) dec_rw_rule
  in

  let table, _old_new_pair =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in

  (* we now create the lhs of the obtained conclusion *)
  (* let fresh_x_var = Vars.make_fresh Type.tmessage "mess" in *)
  let s = (L.mk_loc L._dummy "r_CCA") in
  let ty_args = List.map Vars.ty is in
  let n_fty = Type.mk_ftype_tuple [] ty_args Type.tmessage in
  let table, r =
    let rdef = Symbols.Name { n_fty } in
    Symbols.Name.declare ~approx:true table s ~data:rdef
  in
  let table = Process.add_namelength_axiom table r n_fty in
  None, [], table

(*------------------------------------------------------------------*)
(** {2 Global rewriting} *)

let do_rewrite
    ~(loc : L.t)
    (expand_context : Macros.expand_context)
    (rw : Args.rw_count * Rewrite.rw_rule)
    (s  : TS.sequent)
    (t  : Term.term)
  : Term.term * TS.sequent list
  =
  let mult, rw_erule = rw in
  match
    Rewrite.rewrite_exn 
      ~loc (TS.table s) (TS.params s) (TS.vars s) (TS.system s) expand_context
      (TS.get_trace_hyps s)
      mult rw_erule (Local t)
  with
  | Local t, subs ->
    let subs =
      List.map (fun (sub_system, sub) -> 
          TS.set_conclusion_in_context sub_system sub s
        ) subs
    in
    t, subs

  | Global _, _ -> assert false

  | exception Tactics.Tactic_soft_failure (_,NothingToRewrite) -> t, []


(** Applies a rewrite item *)
let do_rw_item
    (expand_context : Macros.expand_context)
    (rw_item : Args.rw_item) (s : TS.t) (t : Term.term) 
  : Term.term * TS.t list 
  =
  let rw_c,rw_arg = TLT.p_rw_item rw_item s in

  match rw_arg with
  | Rw_rw {loc; subgs; rule} -> 
    let subgs = List.map (fun x -> TS.set_conclusion x s) subgs in

    let t, subgs' = do_rewrite ~loc expand_context (rw_c, rule) s t in
    t, subgs @ subgs'

  | Rw_expand p_arg -> 
    let arg = TLT.p_rw_expand_arg s p_arg in
    let _, t = TLT.expand_term ~mode:expand_context arg s (Local t) (TS.system s) in
    Equiv.any_to_reach t, []
  
  | Rw_expandall _ ->
    let _, t = TLT.expand_term ~mode:expand_context Any s (Local t) (TS.system s) in
    Equiv.any_to_reach t, []    

let do_s_item
    (expand_context : Macros.expand_context)
    (s_item : Args.s_item) (s : TS.t) (t : Term.term) 
  : Term.term 
  =
  match s_item with
  | Args.Simplify _loc, args -> 
    let param = Reduction.rp_default in
    let param = Reduction.parse_simpl_args param args in
    Reduction.reduce_term (TS.Reduce.to_state ~expand_context param s) t 

  | Args.Tryauto loc, _ | Args.Tryautosimpl loc, _ ->
    soft_failure ~loc (Failure "cannot use // or //= in a global rewriting")

let do_rw_arg
    (expand_context : Macros.expand_context)
    (rw_arg : Args.rw_arg) (s : TS.t) (t : Term.term) 
  : Term.term * TS.t list
  =
  match rw_arg with
  | Args.R_item rw_item  -> do_rw_item expand_context rw_item s t
  | Args.R_s_item s_item -> do_s_item  expand_context s_item s t, []

let do_rw_args
    (expand_context : Macros.expand_context)
    (rw_args : Args.rw_arg list) (s : TS.t) (t : Term.term) 
  : Term.term * TS.t list
  =
  List.fold_left (fun (t,subgs) rw_arg ->
      let t, subgs' = do_rw_arg expand_context rw_arg s t in
      t, subgs @ subgs'
    ) (t, []) rw_args


let global_rewrite
    (table   : Symbols.table)
    (sdecl   : Decl.system_modifier)
    (rw      : Args.rw_arg list)
  : Goal.statement option * Goal.t list * Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let context = SE.{ set = (old_system :> arbitrary); pair = None; } in
  
  let subgs = ref [] in

  let fmap (arg : system_map_arg) (_ms : Symbols.macro) (t : Term.term) 
      : Term.term 
    =
    let vars, ts, expand_context = match arg with
      | Macros.ADescr d -> 
         Vars.of_list (Vars.Tag.local_vars d.indices), 
         Term.mk_action d.name (Term.mk_vars d.indices),
         Macros.InSequent
        
      | Macros.AGlobal { is; ts; inputs } ->
         Vars.of_list (Vars.Tag.local_vars (ts :: is @ inputs)), 
         Term.mk_var ts,
         Macros.InGlobal { inputs }
    in
    (* new empty sequent *)
    let env = Env.init ~table ~vars ~system:context () in
    let s = TS.init ~env Term.mk_false in

    (* hypothesis: the timestamp the macro is at happens *)
    let hyp_hap = Equiv.Local (Term.mk_happens ts) in
    (* add [hyp_hap] as hypothesis, so it's available when [do_rewrite] tries to rewrite *)
    let (hyp_hap_id, s_hap) = TS.Hyps.add_i AnyName (LHyp hyp_hap) s in 

    (* hypothesis for global macros: ts is one of the shapes where the action is 
       defined *)
    let (hyp_hap2_oid, s_hap2) =
      match arg with
      | Macros.AGlobal { is = _; ts; ac_descrs; inputs = _ } ->
         let lex =
           List.map
             (fun (acd:Action.descr) -> (* formula: exists indices. ts = ac(indices) *)
               let tts = Term.mk_var ts in
               let ind,_ = Term.refresh_vars acd.indices in 
               let tac = Action.(Term.mk_action acd.name (Term.mk_vars ind)) in
               let eq = Term.mk_eq ~simpl:true tts tac in
               let ex = Term.mk_exists ~simpl:true ind eq in
               ex)
             ac_descrs
         in
         let hyp_hap2 = Equiv.Local (Term.mk_ors ~simpl:true lex) in
         let (hyp_hap2_id, s_hap2) = TS.Hyps.add_i AnyName (LHyp hyp_hap2) s_hap in
         (Some hyp_hap2_id, s_hap2)
      | _ -> (None, s_hap)
    in
    
    (* rewrite, generate subgoals *)
    let t, subgs' = do_rw_args expand_context rw s_hap2 t in
    let subgs' = TraceTactics.tryauto subgs' in (* auto close easy goals *)
    let subgs' = 
      List.map  
        (fun g ->
          let gg = (* if global macro: revert hyp_hap2 *)
            match hyp_hap2_oid with
            | Some i -> LowTactics.TraceLT.revert i g
            | None -> g
          in
          (* revert hyp_hap *)
          let gg = LowTactics.TraceLT.revert hyp_hap_id gg in
          (* rename the timestamp variable *)
          let gg = 
            match arg with
            | Macros.AGlobal {is = _; ts; ac_descrs = _; inputs = _} ->
              let _, new_ts =
                Vars.make `Approx (TS.vars gg) Type.ttimestamp "t" (Vars.Tag.make Vars.Local)
              in 
              TS.rename ts new_ts gg
            | _ -> gg
          in
          gg)
        subgs'
    in
    subgs := subgs' @ !subgs;   (* add new subgoals *)
    t
  in

  let table, _new_system_e =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in 

  let subgs = List.map (fun s -> Goal.Local s) !subgs in
  None, subgs, table


(*------------------------------------------------------------------*)
let declare_system
    (table   : Symbols.table)
    (sdecl   : Decl.system_modifier)
  : Goal.statement option * Goal.t list * Symbols.table
  =
  match sdecl.Decl.modifier with
  | Rename gf         -> global_rename  table sdecl        gf
  | PRF  (bnds, hash) -> global_prf     table sdecl bnds hash
  | CCA  (bnds, enc)  -> global_cca     table sdecl bnds  enc
  | Rewrite rw        -> global_rewrite table sdecl rw
