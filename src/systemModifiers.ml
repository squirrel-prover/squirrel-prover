open Utils

module SE = SystemExpr
module L  = Location

module Pos = Match.Pos
               
module Sv = Vars.Sv
module Sp = Pos.Sp
              
(*------------------------------------------------------------------*)
(** Rewrite a rule as much as possible.
    The rewriting rule can depend on the position in the term. *)
let rewrite
    ~(mode   : [`TopDown of bool | `BottomUp])
    (table   : Symbols.table)
    (system  : SE.t)
    (venv    : Vars.env)         (* for clean variable naming *)
    (mk_rule : Pos.pos -> Rewrite.rw_rule option) 
    (t       : Term.term)
  : Term.term 
  =
  let rw_inst : Match.Pos.f_map = 
    fun occ vars _conds p ->
      (* build the rule to apply at position [p] *)
      match mk_rule p with
      | None -> `Continue
      | Some rule ->
        assert (rule.rw_conds = []);

        let left,right = rule.rw_rw in
        let pat : Term.term Match.pat = Match.{ 
            pat_tyvars = rule.rw_tyvars; 
            pat_vars   = rule.rw_vars; 
            pat_term   = left;
          } 
        in      
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
  let _, f = Match.Pos.map ~mode rw_inst venv t in
  f

(** Simple case of [rewrite], without recursion and with a single rewriting 
    rule. *)
let rewrite_norec
    (table  : Symbols.table)
    (system : SE.t)
    (venv   : Vars.env)         (* for clean variable naming *)
    (rule   : Rewrite.rw_rule) 
    (t      : Term.term)
  : Term.term 
  =
  rewrite ~mode:(`TopDown false) table system venv (fun _ -> Some rule) t
    
(*------------------------------------------------------------------*)
(** High-level system cloning function. *)
let clone_system_map
    (table    : Symbols.table)
    (system   : SE.t)
    (s_system : SE.single_system)
    (new_name : Theory.lsymb)
    (fmap     :
       ( Action.descr ->
         Symbols.macro ->
         Term.term ->
         Term.term ))
  : Symbols.table * SE.t * Symbols.system 
  =
  (* We declare the system *)
  let table, new_system_name =
    SystemExpr.clone_system_map
      table system new_name
      (fun descr -> Action.descr_map (fun _ -> fmap descr) descr)
  in

  let new_s_system, old_s_system, old_system_name =
    match system with
    | Single (Left  s as old) -> SE.Left  new_system_name, old, s
    | Single (Right s as old) -> SE.Right new_system_name, old, s
    |  _ -> assert false
  in

  let global_macro_fold ns dec_def _ table : Symbols.table =
    Macros.update_global_data
      table ns dec_def
      s_system new_s_system fmap
  in

  let table = Symbols.Macro.fold global_macro_fold table table in

  let new_system_e = SystemExpr.pair table old_s_system new_s_system in

  table, new_system_e, old_system_name

(*------------------------------------------------------------------*)
let parse_single_system_name table sdecl =
  match SE.parse_se table sdecl.Decl.from_sys with
  | Single s as res -> res, s
  | _ -> 
    Tactics.soft_failure ~loc:(L.loc sdecl.Decl.from_sys)
      (Failure "a single system must be provided")

(*------------------------------------------------------------------*)
(** Convertion of system modifiers arguments.
    - [bnds] are additional binded variables. *)
let conv_term ?pat table system ~bnds (term : Theory.term)
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
  let t, _ = Theory.convert ?pat conv_env term in
  env.vars, is, t

(*------------------------------------------------------------------*)
let mk_equiv_statement
    table hint_db
    new_axiom_name enrich make_conclusion new_system
  : Goal.statement
  =
  let `Equiv formula, _ =
    Goal.make_obs_equiv ~enrich table hint_db new_system 
  in
  let formula = make_conclusion formula in
  Goal.{ name    = new_axiom_name; 
         system  = new_system; 
         ty_vars = []; 
         formula }

(*------------------------------------------------------------------*)
(** {2 Renaming} *)

let global_rename
    (table : Symbols.table) (hint_db : Hint.hint_db)
    sdecl (gf : Theory.global_formula)
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in
  let env = Env.init ~table ~system:old_system () in
  let conv_env = Theory.{ env; cntxt = InGoal } in

  let f = Theory.convert_global_formula conv_env gf in

  let vs, f = Equiv.Smart.decompose_forall f in

  Vars.check_type_vars vs [Type.Index]
    (fun () -> Tactics.hard_failure ~loc:(L.loc gf)
        (Tactics.Failure "Only index variables can be bound."));

  let ns1, ns2, n1, n2 =
    match f with
    |  Atom (Equiv ([Term.Diff (Term.Name ns1, Term.Name ns2)])) ->
      ns1, ns2, Term.mk_name ns1, Term.mk_name ns2

    | _ ->
      Tactics.hard_failure ~loc:(L.loc gf) (Failure "arguments ill-formed")
  in

  (* We check that n2 does not occur in the old system using fresh. *)
  let cntxt = Constr.{ table;
                       system = old_system;
                       models = None; }
  in
  let iter = new Fresh.find_name ~cntxt true ns2.s_symb in
  let () =
    try
      SystemExpr.iter_descrs
        table old_system
        (fun action_descr ->
           iter#visit_message (snd action_descr.output) ;
           iter#visit_message (snd action_descr.condition) ;
           List.iter (fun (_,m) -> iter#visit_message m) action_descr.updates
        );
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
      rw_vars   = Vars.Sv.of_list vs;
      rw_conds  = [];
      rw_rw     = n1', n2';
    }
  in

  let fmap _ _ms t : Term.term =
    rewrite_norec table old_system env.vars rw_rule t
  in
  
  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    "rename_from_" ^ Symbols.to_string old_system_name ^
    "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in

  let make_conclusion equiv =
    let fimpl =
      Equiv.Impl(
        Equiv.mk_forall evars
          (Atom (Equiv [Term.mk_var fresh_x_var; Term.mk_diff n1 n2])),
        equiv)
    in
    `Equiv (Equiv.mk_forall [fresh_x_var] fimpl)
  in

  let lemma =
    mk_equiv_statement
      table hint_db
      axiom_name enrich make_conclusion new_system_e
  in
  (Some lemma, table)


(*------------------------------------------------------------------*)
(** {2 PRF} *)

let global_prf
    (table : Symbols.table)
    (hint_db : Hint.hint_db)
    (sdecl : Decl.system_modifier)
    (bnds  : Theory.bnds)
    (hash  : Theory.term)
  : Goal.statement option * Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let venv, is, hash = conv_term table old_system ~bnds hash in

  let cntxt = Constr.{
      table  = table;
      system = old_system;
      models = None}
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

  (* We first refresh globably the indices to create the left pattern *)
  let is1, left_subst = Term.refresh_vars `Global is in

  let left_key =  Term.subst left_subst (Term.mk_name param.h_key) in
  let left_key_ids = match left_key with
    | Term.Name s -> s.s_indices
    | _ -> assert false
  in
  (* We create the pattern for the hash *)
  let fresh_x_var = Vars.make_new Type.Message "x" in
  let hash_pattern =
    Term.mk_fun table param.h_fn [] [Term.mk_var fresh_x_var; left_key ]
  in

  (* Instantiation of the fresh name *)
  let ndef =
    let ty_args = List.map Vars.ty is in
    Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args Type.Message ; }
  in
  let table,n =
    Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") ndef
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
      rw_rw     = hash_pattern, mk_tryfind;
    }
  in

  let fmap _ _ms t =
    rewrite_norec table old_system venv rw_rule t
  in

  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    "prf_from_" ^ Symbols.to_string old_system_name ^
    "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [Term.mk_var fresh_x_var;
               Term.mk_diff
                 (Term.mk_name param.h_key)
                 (Term.mk_name @@ Term.mk_isymb n Message (is))])
    in
    let concl = 
      Equiv.mk_forall [fresh_x_var]
        (Equiv.Smart.mk_impl ~simpl:false (Equiv.mk_forall is atom) equiv)
    in
    `Equiv concl
  in

  let lemma =
    mk_equiv_statement
      table hint_db
      axiom_name enrich make_conclusion new_system_e
  in

  Some lemma, table


(*------------------------------------------------------------------*)
(** {2 CCA} *)

  
let global_cca
    (table : Symbols.table) (hint_db : Hint.hint_db)
    sdecl bnds (p_enc : Theory.term)
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in
  let venv, is, enc = conv_term table old_system ~bnds p_enc in

  let cntxt = Constr.{
      table  = table;
      system = old_system;
      models = None }
  in

  let enc_fn, enc_key, plaintext, enc_pk, enc_rnd =
    match enc with
    | Term.Fun ((fnenc,eis), _,
                [m; Term.Name r;
                 Term.Fun ((fnpk,is), _, [Term.Name sk])])
      when Symbols.is_ftype fnpk Symbols.PublicKey table &&
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
  let ndef =
    let ty_args = List.map Vars.ty enc_rnd.s_indices in
    Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args Type.Message ; }
  in
  let table,n =
    Symbols.Name.declare table (L.mk_loc L._dummy "n_CCA") ndef
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
      rw_rw     = enc, new_enc;
    }
  in
  let dec_rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_vars   = Vars.Sv.of_list (fresh_x_var :: is1);
      rw_conds  = [];
      rw_rw     = dec_pattern, tryfind_dec;
    }
  in

  let fmap _ _ms t =
    rewrite_norec table old_system venv enc_rw_rule t |>
    rewrite_norec table old_system venv dec_rw_rule 
  in

  let table, new_system_e, old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in

  let axiom_name =
    "cca_from_" ^ Symbols.to_string old_system_name ^
    "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_new Type.Message "mess" in
  let rdef =
    let ty_args = List.map Vars.ty is in
    Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args Type.Message ; }
  in
  let table,r =
    Symbols.Name.declare table (L.mk_loc L._dummy "r_CCA") rdef
  in

  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [ Term.mk_var fresh_x_var;
                
                Term.mk_diff
                 (Term.mk_name enc_key)
                 (Term.mk_name @@ Term.mk_isymb n Message (is));
                
               Term.mk_diff
                 (Term.mk_name enc_rnd)
                 (Term.mk_name @@ Term.mk_isymb r Message (is))])
    in
    let concl = Equiv.Impl (Equiv.mk_forall is atom, equiv) in      
    `Equiv (Equiv.mk_forall [fresh_x_var] concl)
  in

  let lemma =
    mk_equiv_statement
      table hint_db
      axiom_name enrich make_conclusion new_system_e
  in
  Some lemma, table

(*------------------------------------------------------------------*)
(** {2 Global PRF with time} *)

let check_fv_finite (fv : Vars.vars) =
  List.iter (fun v ->
      if not (Type.equal (Vars.ty v) Type.tindex) &&
         not (Type.equal (Vars.ty v) Type.ttimestamp) then
        Tactics.hard_failure
          (Failure
             "system contain quantifiers over types ≠ from \
              Index and Timestamp, which are not supported.")
    ) fv


(*------------------------------------------------------------------*)

(** Extended hash occurrence *)
type x_hash_occ = {
  (* macro of the occurrence *)
  x_msymb : Symbols.macro;

  (* macro definition of the occurrence *)
  x_mdef : Symbols.macro_def;

  x_a : Symbols.action;
  (* action of the occurrence *)

  x_a_is : Vars.vars;
  (* action indices of the occurrence *)

  (* the occurrence *)
  x_occ : Iter.hash_occ;

  (* the associated generated name (≠ for all extended hash occurrences) *)
  x_nsymb : Symbols.Name.ns Symbols.t;
}

(*------------------------------------------------------------------*)
(** Hash occurrences with unique identifiers *)
module XO : sig
  type t = private { cnt : x_hash_occ; tag : int; }

  val mk : x_hash_occ -> t
end = struct
  type t = { cnt : x_hash_occ; tag : int; }

  (* create fresh identifiers *)
  let mk =
    let cpt = ref 0 in
    fun cnt -> { cnt; tag = ((incr cpt); !cpt); }
end

(** Strict pre-ordering over hash occurrences, resulting from the 
    pre-order underlying the protocol well-foundness *)
let xo_lt
    (table : Symbols.table) (system : SE.t)
    (x : XO.t) (y : XO.t)
  : bool
  =
  let x, y = x.cnt, y.cnt in

  if x.x_msymb = y.x_msymb then
    (* If we compare the same macros, at the same action, only look for
       subterm ordering constraints. *)
    begin
      if Symbols.is_global x.x_mdef && Symbols.is_global y.x_mdef then
        assert (x.x_a = y.x_a);   (* TODO: is this indeed an invariant? *)

      x.x_a = y.x_a &&
      (let px = Sp.choose x.x_occ.occ_pos
       and py = Sp.choose y.x_occ.occ_pos in
       (* Checking for a single position is enough *)
       Pos.lt px py)
    end
    
  else
    (* Otherwise, unroll [y] definition and look whether [x] appears *)
    
    (* create a [msymb] with new (fresh) indices for [y] *)
    let ms_y =
      Term.mk_isymb
        y.x_msymb
        (Macros.ty_out table y.x_msymb)
        (List.map (fun ty ->
             Vars.make_new ty "a"
           ) (Macros.ty_args table y.x_msymb))
    in
    let a_y = Term.mk_action y.x_a y.x_a_is in

    let cntxt = Constr.{ table; system; models = None } in
    let t_y =
      match Macros.get_definition cntxt ms_y a_y with
      | `Def t -> t
      | _ -> assert false       (* must be defined here *)
    in

    (* search if the macro [x.x_msymb] appears in [t_y] *)
    let rec search (t : Term.term) : bool =
      match t with
      | Macro (ms, _, ts) ->
        if ms.s_symb = x.x_msymb then
          match ts with
          | Term.Action (a, _) ->
            if Symbols.is_global x.x_mdef then
              assert (x.x_a = a);   (* TODO: is this indeed an invariant? *)
            a = x.x_a
          | _ -> false
        else
          begin
            match Macros.get_definition cntxt ms ts with
            | `Def ty -> search ty
            | _ -> false
          end

      (* recurse *)
      | _ -> Term.tfold (fun t found -> found || search t) t false
    in
    search t_y

(*------------------------------------------------------------------*)
(** Maps over hash occurrences *)
module Mxo = Map.Make(struct
    type t = XO.t
    let compare (x : XO.t) (y : XO.t) = Stdlib.compare x.tag y.tag
  end)

(*------------------------------------------------------------------*)
(** A hash occurrence graph.
    There is an edge [(v → u) ∈ m] iff [List.mem v (List.find u m)]. *)
type xomap = XO.t list Mxo.t

(** [cmp x y] iff [(x → y)] *)
let map_from_cmp (cmp : XO.t -> XO.t -> bool) (xs : XO.t list) : xomap =
  let add (map : xomap) (x : XO.t) : xomap =
    let map = Mxo.mapi (fun y s -> if cmp x y then x :: s else s) map in
    let lx =
      Mxo.fold (fun y _ lx -> if cmp y x then y :: lx else lx) map []
    in
    Mxo.add x lx map
  in
  List.fold_left add Mxo.empty xs

(** Comparison in the transitive closure, i.e. [x →* y]. *)
let rec lt_map (map : xomap) (x : XO.t) (y : XO.t) =
  if not (Mxo.mem y map) then false
  else
    let ly = Mxo.find y map in
    List.exists (fun (z : XO.t) -> x.tag = z.tag || lt_map map x z) ly

(** [x] and [y] incomparable w.r.t. the transitive closure of [map]. *)
let incomparable map x y = not (lt_map map x y) && not (lt_map map y x) 

(** Linearize the partial ordering [map].
    I.e. return a total ordering compatible with [map]. *)
let rec linearize (map : xomap) : xomap =
  let exception Found of XO.t * XO.t in
  try
    Mxo.iter (fun x _ ->
        Mxo.iter (fun y _ ->
            if incomparable map x y then raise (Found (x,y))
          ) map
      ) map;
    map    (* map is a lineare ordering *)

  with Found (x,y) ->
    (* x,y incomparable, arbitrarily choose [(y → x)] and add it to the map. *)
    let lx = Mxo.find x map in
    linearize (Mxo.add x (y  :: lx) map)
  
  
(*------------------------------------------------------------------*)
let global_prf_time
    (table : Symbols.table)
    (sdecl : Decl.system_modifier)
    (bnds  : Theory.bnds)
    (hash  : Theory.term)
  : string *
    Term.term list *
    (Equiv.global_form -> [> `Equiv of Equiv.global_form ]) *
    SE.t *
    Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let venv, is, hash = conv_term ~pat:true table old_system ~bnds hash in

  let cntxt = Constr.{
      table;
      system = old_system;
      models = None}
  in

  let param = Prf.prf_param hash in

  (* Check syntactic side condition. *)
  (* TODO: this is not correct, as global macros are not iterated upon by 
     [Euf.key_ssc] *)
  let errors =
    Euf.key_ssc
      ~elems:[] ~allow_functions:(fun x -> false)
      ~cntxt param.h_fn param.h_key.s_symb
  in
  if errors <> [] then
    Tactics.soft_failure (Tactics.BadSSCDetailed errors);

  (* type of the hash function input *)
  let m_ty = List.hd (param.h_fty.fty_args) in

  let mk_occ_name
      (table : Symbols.table)
      (occ   : Iter.hash_occ)
    : Symbols.table * Symbols.name
    =
    (* check that no occurrence of the hash appears below a binder
       with a non-finite type. *)
    check_fv_finite occ.Iter.occ_vars;

    let ndef =
      let ty_args = List.map Vars.ty occ.Iter.occ_vars in
      Symbols.{ n_fty = Type.mk_ftype 0 [] ty_args m_ty ; }
    in
    Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") ndef
  in

  let (table, occs) : Symbols.table * XO.t list =
    SystemExpr.fold_descrs (fun descr (table,occs) ->
        Iter.fold_descr ~globals:true (fun ms m_is mdef t (table,occs) ->
            (* find new occurrences *)
            let new_occs =
              Iter.get_f_messages_ext
                ~fv:descr.indices ~cntxt
                param.h_fn param.h_key.s_symb t
            in

            (* extend new occurrences with additional information *)
            let table, new_occs =
              List.map_fold (fun table occ ->
                  let table, x_nsymb = mk_occ_name table occ in
                  table,
                  XO.mk {
                    x_msymb = ms;
                    x_mdef  = mdef;
                    x_occ   = occ;
                    x_nsymb;
                    x_a     = descr.name;
                    x_a_is  = descr.indices;
                  }
                ) table new_occs
            in
            table, new_occs @ occs
          ) table old_system descr (table,occs)
      ) table old_system (table,[])
  in

  (* FIXME: check duplicate module alpha-renaming 
     (merge [occ.occ_pos] which are duplicated) *)
  let occs = List.remove_duplicate (=) occs in

  (* fresh variable representing the hashed message to rewrite *)
  let x = Vars.make_new m_ty "x" in
  let x_t = Term.mk_var x in
  
  (* timestamp at which [H(x,k)] occurs  *)
  let tau = Vars.make_new Type.ttimestamp "t" in
  let tau_t = Term.mk_var tau in

  let is, subst = Term.refresh_vars `Global is in
  let key = Term.subst subst (Term.mk_name param.h_key) in
  let key_is = List.map (Term.subst_var subst) param.h_key.s_indices in

  (* term to rewrite *)
  let to_rw =
    Term.mk_fun table param.h_fn [] [x_t; key ]
  in

  (* name term associated to a hash occurrence. *)
  let mk_occ_term (xocc : XO.t) : Term.term =
    Term.mk_name (Term.mk_isymb xocc.cnt.x_nsymb m_ty xocc.cnt.x_occ.occ_vars)
  in

  (* action term at associated to a hash occurrence. *)
  let mk_occ_ts (xocc : XO.t) : Term.term =
    Term.mk_action xocc.cnt.x_a xocc.cnt.x_a_is
  in

  (* compute the constraints maps between hash occurrences, resulting
     from the protocol definition. *)
  let map_cnstrs = map_from_cmp (xo_lt table old_system) occs in

  (* arbitrary linearization of the map *)
  let map_cnstrs = linearize map_cnstrs in

  (* Condition checking whether [(tau1, s1) < (tau2, s2)].
     We use the lexicographic order [(Term.mk_lt, mt_map map_cnstrs)]. *)
  let mk_xocc_lt
      (tau1 : Term.term) (xocc1 : XO.t)
      (tau2 : Term.term) (xocc2 : XO.t)
    : Term.term
    =
    if lt_map map_cnstrs xocc1 xocc2 then
      Term.mk_leq tau1 tau2
    else
      Term.mk_lt tau1 tau2
  in

  let mk_xocc_collision
      (tau1 : Term.term) (xocc1 : XO.t)
      (tau2 : Term.term) (xocc2 : XO.t)
    : Term.term
    = 
    (* condition stating that [x] is equal to a hash occurrence [xocc]. *)
    let occ_vars, occ_t = xocc1.cnt.x_occ.occ_cnt in
    let msg_eq = 
    Term.mk_ands ~simpl:false
      [ Term.mk_eq ~simpl:true x_t occ_t;                 (* hash content equ. *)
        Term.mk_indices_eq ~simpl:true key_is occ_vars;   (* hash key equ. *)
        Term.mk_eq ~simpl:true tau_t (mk_occ_ts xocc1); ] (* timestamp equ. *)
    in
    let xocc_lt = mk_xocc_lt tau1 xocc1 tau2 xocc2 in
    Term.mk_and ~simpl:false msg_eq xocc_lt 
  in
  
  (* we rewrite [H(x,k)] at occurrence [s0] at time [tau0] into:
     [
       try find tau, occ s.t. (tau,s) < (tau0,s0) && x = s_{occ} 
       then n_{occ}@tau
       else n_occ0@tau0
     ] *)
  let rw_target
      (tau0_t : Term.term)
      (xocc0  : XO.t)
    =
    let cond =
      (* We check whether there exists [(tau,s)] such that:
         [(tau,s) < (tau0,s0) && x = s_x] *)
      Term.mk_ors
        (List.map (fun xocc ->
             mk_xocc_collision tau_t xocc tau0_t xocc0
           ) occs)
    in
    let t_else = mk_occ_term xocc0 in
    let t_then =
      List.fold_left (fun t_then xocc ->
          let t_cond = mk_xocc_collision tau_t xocc tau0_t xocc0 in
          let t_occ = mk_occ_term xocc in
          Term.mk_ite ~simpl:false t_cond t_occ t_then
        ) (Term.mk_witness m_ty) occs
      
    in
    Term.mk_find [tau] cond t_then t_else
  in

  (* - [tau0] is the time at which the term being rewritten in is 
       evaluated. 
       E.g., if we rewrite in the body of [output@A(i)] then [tau0] 
       is [A(i)]. 
     - [pos] is the position at which we are trying to do the rewrite, 
       which is necessary to retrieve the associated fresh name. *)
  let mk_rw_rule (tau0 : Term.term) (pos : Pos.pos) : Rewrite.rw_rule option =
    let hash_occ =
      List.find_opt (fun (xocc : XO.t) ->
          Sp.mem pos xocc.cnt.x_occ.occ_pos
        ) occs
    in
    match hash_occ with
    (* not an interesting position, no rewriting to do *)
    | None -> None

    (* interesting position, retrieve the associated occurrence *)
    | Some xocc ->
      let rule = Rewrite.{
          rw_tyvars = [];
          rw_vars   = Sv.of_list (x :: is);
          rw_conds  = [];
          rw_rw     = (to_rw, rw_target tau0 xocc); }
      in
      Some rule
  in

  let fmap (d : Action.descr) (ms : Symbols.macro) (t : Term.term) : Term.term =
    let tau0 = Term.mk_action d.name d.indices in

    (* To keep meaningful positions, we need to do the rewriting bottom-up.
       Indeed, this ensures that a rewriting does not modify the positions
       of the sub-terms above the position the rewriting occurs at. *)
    rewrite ~mode:`BottomUp table old_system venv (mk_rw_rule tau0) t
  in

  let _table, _new_system_e, _old_system_name =
    clone_system_map
      table old_system old_single_system sdecl.Decl.name fmap
  in 
  assert false

(*------------------------------------------------------------------*)
let declare_system
    (table   : Symbols.table)
    (hint_db : Hint.hint_db)
    (sdecl   : Decl.system_modifier)
  : Goal.statement option * Symbols.table
  =
  let lemma, table = 
    match sdecl.Decl.modifier with
    | Rename gf        -> global_rename table hint_db sdecl        gf
    | PRF (bnds, hash) -> global_prf    table hint_db sdecl bnds hash
    | CCA (bnds, enc)  -> global_cca    table hint_db sdecl bnds  enc
  in
  lemma, table
