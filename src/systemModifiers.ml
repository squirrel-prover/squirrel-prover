open Utils

module Name = NameOccs.Name
                
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
  
  Rewrite.high_rewrite ~mode:(`TopDown false) ~strict:false table env system mk_rule t
    

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
    (new_name : Theory.lsymb)
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

  let old_new_pair = SE.make_pair system new_single_system in

  let global_macro_fold
      (ns : Symbols.macro) (dec_def : Symbols.macro_def) 
      (_ : Symbols.data) (table : Symbols.table)
    : Symbols.table 
    =
    Macros.update_global_data table ns dec_def system new_single_system fmap
  in

  let table = Symbols.Macro.fold global_macro_fold table table in

  table, old_new_pair

(*------------------------------------------------------------------*)
let parse_single_system_name table sdecl : SE.fset * System.Single.t =
  let res = SE.Parse.parse table sdecl.Decl.from_sys in
  match SE.(to_list (to_fset res)) with
  | [_,s] -> SE.to_fset res, s
  | _ ->
    soft_failure ~loc:(L.loc sdecl.Decl.from_sys)
      (Failure "a single system must be provided")

(*------------------------------------------------------------------*)
(** Convertion of system modifiers arguments.
    - [bnds] are additional binded variables. *)
let conv_term ?pat table system ~bnds (term : Theory.term)
  : Vars.vars * Term.term
  =
  let env = Env.init ~table ~system:system () in
  let env,is = Theory.convert_bnds (Vars.Tag.make Vars.Local) env bnds in

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
  is, t

(*------------------------------------------------------------------*)
let mk_equiv_statement
    table 
    new_axiom_name enrich make_conclusion new_system
  : Goal.statement
  =
  let context = SE.equivalence_context ~set:new_system new_system in
  let formula =
    fst (Goal.make_obs_equiv ~enrich table context)
    |> Equiv.any_to_equiv
  in
  let formula = make_conclusion formula in
  Goal.{ name    = new_axiom_name; 
         system  = context; 
         ty_vars = []; 
         formula }


(*------------------------------------------------------------------*)
(** {2 Renaming} *)

let global_rename
    (table : Symbols.table) 
    sdecl (gf : Theory.global_formula)
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  (* Convert equivalence formula [gf].
     We parse it with old_single_system on both sides,
     but any system would work here since the equivalence must
     relate names. *)
  let system =
    SE.equivalence_context (SE.make_pair old_single_system old_single_system) in
  let env = Env.init ~table ~system () in
  let conv_env = Theory.{ env; cntxt = InGoal } in
  let f = Theory.convert_global_formula conv_env gf in

  (* Decompose it as universally quantified equivalence over names. *)
  let vs, f = Equiv.Smart.decompose_forall f in
  Vars.check_type_vars vs [Type.Index]
    (fun () -> Tactics.hard_failure ~loc:(L.loc gf)
        (Tactics.Failure "Only index variables can be bound."));
  let _ns1, ns2, n1, n2 =
    match f with
    |  Atom
        (Equiv ([Term.Diff (Explicit [_,(Term.Name _ as ns1);
                                      _, (Term.Name _ as ns2)])]))
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
           List.iter (fun (_,_,m) -> iter#visit_message m) action_descr.updates)
    with OldFresh.Deprecated_Name_found ->
      Tactics.hard_failure
        (Tactics.Failure "The name on the right-hand side already \
                          occurs in the left-hand side.")
  in

  (* We now build the rewrite rule *)
  let evars = Term.get_vars n1 in
  let vs, subs = Term.refresh_vars evars in
  let n1', n2' = (Term.subst subs n1, Term.subst subs n2) in
  let rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_system = SE.any;
      rw_vars   = Vars.Tag.local_vars vs;
      rw_conds  = [];
      rw_rw     = n1', n2';
    }
  in

  let fmap _ _ms t : Term.term =
    high_rewrite_norec table (old_system :> SE.t) rw_rule t
  in
  
  let table, old_new_pair =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    let old_system_name = Symbols.to_string old_single_system.system in
    "rename_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_fresh Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in

  let make_conclusion equiv =
    let fimpl =
      Equiv.Impl(
        Equiv.Smart.mk_forall_tagged
          (Vars.Tag.global_vars ~const:true evars)
          (* FIXME: unclear what tags should be used here *)
          (Atom (Equiv [Term.mk_var fresh_x_var;
                        Term.mk_diff [Term.left_proj,n1;Term.right_proj,n2]])),
        equiv)
    in
    Equiv.Global (Equiv.Smart.mk_forall [fresh_x_var] fimpl)
  in
  let lemma =
    mk_equiv_statement
      table
      axiom_name enrich make_conclusion old_new_pair
  in
  (Some lemma, [], table)


(*------------------------------------------------------------------*)
(** {2 PRF} *)

let global_prf
    (table : Symbols.table)
    (sdecl : Decl.system_modifier)
    (bnds  : Theory.bnds)
    (hash  : Theory.term)
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

  let param = Prf.prf_param hash in

  (* Check syntactic side condition. *)
  let errors =
    OldEuf.key_ssc ~globals:true
      ~elems:[] ~allow_functions:(fun _ -> false)
      ~cntxt param.h_fn param.h_key.symb.s_symb
  in
  if errors <> [] then
    soft_failure (Tactics.BadSSCDetailed errors);

  (* We first refresh globably the indices to create the left pattern *)
  let is1, left_subst = Term.refresh_vars is in

  let left_key =  Term.subst left_subst (Name.to_term param.h_key) in
  let left_key_ids =
    match left_key with
    | Term.Name (_,ids) -> ids
    | _ -> assert false
  in
  (* We create the pattern for the hash *)
  let fresh_x_var = Vars.make_fresh Type.Message "x" in
  let hash_pattern =
    Term.mk_fun_tuple table param.h_fn [Term.mk_var fresh_x_var; left_key ]
  in

  (* Instantiation of the fresh name *)
  let ndef =
    let ty_args = List.map Vars.ty is in
    Symbols.{ n_fty = Type.mk_ftype_tuple [] ty_args Type.Message ; }
  in
  let table,n =
    Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") ndef
  in
  
  (* the hash h of a message m will be replaced by tryfind is s.t = fresh mess
     in fresh else h *)
  let mk_tryfind =
    let ns = Term.mk_symb n Message in
    Term.mk_find is Term.(
        mk_and
          (mk_atom `Eq (Term.mk_var fresh_x_var) param.h_cnt)
          (mk_eqs left_key_ids param.h_key.args)
      ) (Term.mk_name ns (Term.mk_vars is)) hash_pattern
  in
  let rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_system = SE.any;
      rw_vars   = Vars.Tag.local_vars (fresh_x_var :: is1);
      rw_conds  = [];
      rw_rw     = hash_pattern, mk_tryfind;
    }
  in

  let fmap _ _ms t =
    high_rewrite_norec table (old_system :> SE.t) rw_rule t
  in

  let table, old_new_pair =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in 
  
  let axiom_name =
    let old_system_name = Symbols.to_string old_single_system.system in
    "prf_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
  in

  (* we now create the lhs of the obtained conclusion *)
  let fresh_x_var = Vars.make_fresh Type.Message "mess" in
  let enrich = [Term.mk_var fresh_x_var] in
  let make_conclusion equiv =
    let atom =
      Equiv.Atom (
        Equiv [Term.mk_var fresh_x_var;
               Term.mk_diff
                 [Term.left_proj, Name.to_term param.h_key;
                  Term.right_proj,
                  Term.mk_name
                    (Term.mk_symb n Message) (Term.mk_vars is)]])
    in
    let concl = 
      Equiv.Smart.mk_forall [fresh_x_var]
        (Equiv.Smart.mk_impl ~simpl:false
           (Equiv.Smart.mk_forall_tagged
              (* FIXME: unclear what tags should be used here *)
              (Vars.Tag.global_vars ~const:true is) atom)
           equiv)
    in
    Equiv.Global concl
  in

  let lemma =
    mk_equiv_statement
      table
      axiom_name enrich make_conclusion old_new_pair
  in

  Some lemma, [], table



(*------------------------------------------------------------------*)
(** {2 CCA} *)

  
let global_cca
    (table : Symbols.table) 
    sdecl bnds (p_enc : Theory.term)
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
    | Term.Fun (fnenc, _,
                [Tuple [m; Term.Name _ as r;
                        Term.Fun (fnpk, _, [Term.Name _ as sk])]])
      when Symbols.is_ftype fnpk Symbols.PublicKey table &&
           Symbols.is_ftype fnenc Symbols.AEnc table ->
      fnenc, Name.of_term sk, m, fnpk, Name.of_term r

    | _ ->
      soft_failure ~loc:(L.loc p_enc)
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

  (* TODO: check randomness is used only once, and message is distinct. *)

  (* We first refresh globably the indices to create the left patterns *)
  let is1, left_subst = Term.refresh_vars is in

  (* The dec must match all decryption with the corresponding secret key *)
  let fresh_x_var = Vars.make_fresh Type.Message "x" in
  let dec_pattern =
    Term.mk_fun_tuple table dec_fn [ Term.mk_var fresh_x_var;
                                     Name.to_term enc_key ]
  in
  let dec_pattern = Term.subst left_subst dec_pattern in

  (* Instantiation of the fresh replacement *)
  let ndef =
    let ty_args = List.map Term.ty enc_rnd.args in
    Symbols.{ n_fty = Type.mk_ftype_tuple [] ty_args Type.Message ; }
  in
  let table,n =
    Symbols.Name.declare table (L.mk_loc L._dummy "n_CCA") ndef
  in
  
  let mess_replacement =
    if Term.is_name plaintext then
      let ns = Term.mk_symb n Message in
      Term.mk_name ns enc_rnd.args
    else
      Term.mk_zeroes (Term.mk_len plaintext) in

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

  let enc_rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_system = SE.any;
      rw_vars   = Vars.Tag.local_vars is;
      rw_conds  = [];
      rw_rw     = enc, new_enc;
    }
  in
  let dec_rw_rule = Rewrite.{
      rw_tyvars = [];
      rw_system = SE.any;
      rw_vars   = Vars.Tag.local_vars (fresh_x_var :: is1);
      rw_conds  = [];
      rw_rw     = dec_pattern, tryfind_dec;
    }
  in

  let fmap _ _ms t =
    high_rewrite_norec table (old_system :> SE.t) enc_rw_rule t |>
    high_rewrite_norec table (old_system :> SE.t) dec_rw_rule
  in

  let table, _old_new_pair =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in

  (* Note: the added lemma was bugged, commented out for now. *)
  (* let axiom_name =
   *   let old_system_name = Symbols.to_string old_single_system.system in
   *   "cca_from_" ^ old_system_name ^ "_to_" ^ Location.unloc sdecl.name
   * in *)

  (* we now create the lhs of the obtained conclusion *)
  (* let fresh_x_var = Vars.make_fresh Type.Message "mess" in *)
  let table, _r =
    let rdef =
      let ty_args = List.map Vars.ty is in
      Symbols.{ n_fty = Type.mk_ftype_tuple [] ty_args Type.Message ; }
    in
    Symbols.Name.declare table (L.mk_loc L._dummy "r_CCA") rdef
  in

  (* let enrich = [Term.mk_var fresh_x_var] in
   * let make_conclusion equiv =
   *   let atom =
   *     Equiv.Atom (
   *       Equiv [ Term.mk_var fresh_x_var;
   *               
   *               Term.mk_diff
   *                 [Term.left_proj, Name.to_term enc_key;
   *                  Term.right_proj, Name.to_term @@ Term.mk_symb n Message is];
   *               
   *              Term.mk_diff
   *                [Term.left_proj, Name.to_term enc_rnd;
   *                 Term.right_proj, Name.to_term @@ Term.mk_symb r Message is] ])
   *   in
   *   let concl = Equiv.Impl (Equiv.mk_forall is atom, equiv) in      
   *   Equiv.Global (Equiv.mk_forall [fresh_x_var] concl)
   * in *)

  (* let lemma =
   *   mk_equiv_statement
   *     table hint_db
   *     axiom_name enrich make_conclusion old_new_pair
   * in *)
  (* Some lemma *) None, [], table

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

  (* associated generated name, which is ≠ for all extended hash occs., 
     except for global macros, where the same name is used for the same
     global macro appearing in different (mutually exclusive) branches. *)
  x_nsymb : Symbols.name;
}

let pp_x_hash_occ fmt (x : x_hash_occ) : unit =
  Fmt.pf fmt "@[<v>action: %a(%a) :- %a@;\
              fresh name: %a@;\
              %a@]"
    Symbols.pp x.x_a
    Vars.pp_list x.x_a_is
    Symbols.pp x.x_msymb
    Symbols.pp x.x_nsymb
    Iter.pp_hash_occ x.x_occ

let subst_xocc (s : Term.subst) (o : x_hash_occ) : x_hash_occ =
  let occ = o.x_occ in
  let x_a_is = Term.subst_vars s o.x_a_is in
  let is, t = occ.occ_cnt in
  let x_occ = Iter.{ 
      occ with
      occ_vars = Term.subst_vars s occ.occ_vars;
      occ_cnt = List.map (Term.subst s) is, Term.subst s t;
      occ_cond = List.map (Term.subst s) o.x_occ.occ_cond;
    } 
  in
  { o with x_a_is; x_occ; }


let refresh_xocc (o : x_hash_occ) : Term.subst * x_hash_occ =
  let occ = o.x_occ in
  assert (Sv.subset (Sv.of_list o.x_a_is) (Sv.of_list occ.occ_vars));

  let _, subst = Term.refresh_vars occ.occ_vars in

  subst, subst_xocc subst o

(*------------------------------------------------------------------*)
(** Hash occurrences with unique identifiers *)
module XO : sig
  type t = private { cnt : x_hash_occ; tag : int; }

  val mk : x_hash_occ -> t

  val compare : t -> t -> int

  val subst : Term.subst -> t -> t

  val refresh : t -> Term.subst * t

  val pp : Format.formatter -> t -> unit
end = struct
  type t = { cnt : x_hash_occ; tag : int; }

  let pp fmt (x : t) : unit =
    Fmt.pf fmt "%d: @[%a@]" x.tag pp_x_hash_occ x.cnt

  (* create fresh identifiers *)
  let mk =
    let cpt = ref 0 in
    fun cnt -> { cnt; tag = ((incr cpt); !cpt); }

  let compare (x : t) (y : t) = Stdlib.compare x.tag y.tag

  let subst s x = { x with cnt = subst_xocc s x.cnt }

  let refresh x = 
    let subst, cnt = refresh_xocc x.cnt in
    subst, { x with cnt }
end

(** Strict pre-ordering over hash occurrences, resulting from the 
    pre-order underlying the protocol well-foundness *)
let xo_lt
    (table : Symbols.table) (system : SE.fset)
    (x : XO.t) (y : XO.t)
  : bool
  =
  
  let x, y = x.cnt, y.cnt in

  if x.x_msymb = y.x_msymb then
    (* If we compare the same macros, at the same action, only look for
       subterm ordering constraints. *)
    x.x_a = y.x_a &&
    (let px = Sp.choose x.x_occ.occ_pos
     and py = Sp.choose y.x_occ.occ_pos in
     (* Checking for a single position is enough *)
     Pos.lt px py)
    
  else
    (* Otherwise, unroll [y] definition and look whether [x] appears *)
    
    (* create a [msymb] with new (fresh) indices for [y] *)
    let ms_y =
      Term.mk_symb
        y.x_msymb
        (Macros.ty_out table y.x_msymb)
    in
    let ms_y_args =
      List.map (fun ty ->
          Term.mk_var (Vars.make_fresh ty "a")
        ) (Macros.ty_args table y.x_msymb)
    in
    let a_y = Term.mk_action y.x_a (Term.mk_vars y.x_a_is) in

    let cntxt = Constr.{ table; system; models = None } in
    let t_y =
      match Macros.get_definition cntxt ms_y ~args:ms_y_args ~ts:a_y with
      | `Def t -> t
      | _ -> assert false       (* must be defined here *)
    in

    (* search if the macro [x.x_msymb] appears in [t_y] *)
    let rec search (t : Term.term) : bool =
      match t with
      | Macro (ms, ms_args, ts) ->
        if ms.s_symb = x.x_msymb then
          match ts with
          | Term.Action (a, _) -> a = x.x_a
          | _ -> false
        else
          begin
            match Macros.get_definition cntxt ms ~args:ms_args ~ts with
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
    let compare = XO.compare
  end)

(*------------------------------------------------------------------*)
(** A hash occurrence graph.
    There is an edge [(v → u) ∈ m] iff [List.mem v (List.find u m)]. *)
type xomap = XO.t list Mxo.t

let[@warning "-32"] pp_xomap fmt (map : xomap) : unit =
  let pp_el fmt (u, vs) =
    Fmt.pf fmt "@[[%a → %a]@]" XO.pp u (Fmt.list XO.pp) vs
  in
  Fmt.pf fmt "@[<v>%a@]" (Fmt.list pp_el) (Mxo.bindings map)
  
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

(** Comparison in the transitive closure, i.e. [x →+ y]. *)
let rec lt_map (map : xomap) (x : XO.t) (y : XO.t) =
  if not (Mxo.mem y map) then false
  else
    let ly = Mxo.find y map in
    List.exists (fun (z : XO.t) -> x.tag = z.tag || lt_map map x z) ly

(** [x] and [y] incomparable w.r.t. the transitive closure of [map]. *)
let incomparable map (x : XO.t) (y : XO.t) =
  x.tag <> y.tag &&
  not (lt_map map x y) && not (lt_map map y x) 

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
(* check that at most one hash occurrence appears per macro *)
let check_uniq _table (map : XO.t list) = 
  List.for_all (fun (x : XO.t) ->
      List.for_all (fun (y : XO.t) -> 
          x.tag = y.tag ||
          let x, y = x.cnt, y.cnt in
          x.x_msymb <> y.x_msymb || x.x_a <> y.x_a
        ) map
    ) map

(*------------------------------------------------------------------*)
let global_prf_t
    (table   : Symbols.table)
    (sdecl   : Decl.system_modifier)
    (bnds    : Theory.bnds)
    (hash    : Theory.term)
  : Goal.statement option * Goal.t list * Symbols.table
  =
  let old_system, old_single_system =
    parse_single_system_name table sdecl
  in

  let is, hash =
    let context = SE.(reachability_context (singleton old_single_system)) in
    conv_term ~pat:true table context ~bnds hash 
  in

  let cntxt = Constr.{
      table;
      system = old_system;
      models = None}
  in

  let param = Prf.prf_param hash in

  (* Check syntactic side condition.
     We iter over global macros too ! *)
  let errors =
    OldEuf.key_ssc ~globals:true
      ~elems:[] ~allow_functions:(fun _ -> false)
      ~cntxt param.h_fn param.h_key.symb.s_symb
  in
  if errors <> [] then
    soft_failure (Tactics.BadSSCDetailed errors);

  (* type of the hash function input *)
  let m_ty = match param.h_fty.fty_args with
    | [Type.Tuple [m_ty; _]] -> m_ty
    | _ -> assert false
  in

  let mk_occ_name
      (table : Symbols.table)
      (occ   : Iter.hash_occ)   (* new occurrence *)
      (ms    : Symbols.macro)   (* macro the new occ. appears in *)
      (occs  : XO.t list)       (* already computed occurrences *)
    : Symbols.table * Symbols.name
    =
    (* check that no occurrence of the hash appears below a binder
       with a non-finite type. *)
    check_fv_finite occ.Iter.occ_vars;

    try
      (* for global macros, we use the same name for the same global macro
         appearing in different (mutually exclusive) branches of the system. *)
      let x = 
        List.find (fun x -> 
            Macros.is_global table ms && x.XO.cnt.x_msymb = ms
          ) occs 
      in
      table, x.cnt.x_nsymb 
    with Not_found ->
      let ndef =
        let ty_args = List.map Vars.ty occ.Iter.occ_vars in
        Symbols.{ n_fty = Type.mk_ftype_tuple [] ty_args m_ty ; }
      in
      Symbols.Name.declare table (L.mk_loc L._dummy "n_PRF") ndef
  in

  let (table, occs) : Symbols.table * XO.t list =
    SystemExpr.fold_descrs (fun descr (table,occs) ->
        Iter.fold_descr ~globals:true (fun ms _a_is _m_is mdef t (table,occs) ->
            (* find new occurrences using NoDelta, as we also fold over 
               global macros. *)
            let new_occs =
              Iter.deprecated_get_f_messages_ext ~mode:`NoDelta
                ~fv:descr.indices 
                (old_system :> SE.arbitrary) table
                param.h_fn param.h_key.symb.s_symb t
            in

            (* extend new occurrences with additional information *)
            let table, new_occs =
              List.map_fold (fun table occ ->
                  let table, x_nsymb = mk_occ_name table occ ms occs in
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
  let x = Vars.make_fresh m_ty "x" in
  let x_t = Term.mk_var x in
  
  (* timestamp at which [H(x,k)] occurs  *)
  let tau = Vars.make_fresh Type.ttimestamp "t" in
  let tau_t = Term.mk_var tau in

  let is, subst = Term.refresh_vars is in
  let key = Term.subst subst (Name.to_term param.h_key) in
  let key_is = List.map (Term.subst subst) param.h_key.args in

  (* term to rewrite *)
  let to_rw =
    Term.mk_fun_tuple table param.h_fn [x_t; key ]
  in

  (* name term associated to a hash occurrence. *)
  let mk_occ_term (xocc : XO.t) : Term.term =
    Term.mk_name
      (Term.mk_symb xocc.cnt.x_nsymb m_ty)
      (Term.mk_vars xocc.cnt.x_occ.occ_vars)
  in

  (* action term at associated to a hash occurrence. *)
  let mk_occ_ts (xocc : XO.t) : Term.term =
    Term.mk_action xocc.cnt.x_a (Term.mk_vars xocc.cnt.x_a_is)
  in

  (* compute the constraints maps between hash occurrences, resulting
     from the protocol definition. 
     An occurrence [x] is smaller than [y] w.r.t. [map_cnstrs] if 
     [x] must be computed before [y]. *)
  let map_cnstrs = map_from_cmp (xo_lt table old_system) occs in
 
  (* arbitrary linearization of the map *)
  let map_cnstrs = linearize map_cnstrs in

  (* Occurrences sorted according to the computation order. *)
  let occs = 
    List.sort_uniq (fun (x : XO.t) (y : XO.t) ->
        if x.tag = y.tag then 0 
        else if lt_map map_cnstrs x y then -1 else 1
      ) occs 
  in

  if not (check_uniq table occs) then
    Tactics.hard_failure 
      (Failure
         "there are several hash occurrence in the same macro \
          (maybe try adding let bindings).");

  let rec lt_lex (is1 : Vars.vars) (is2 : Vars.vars) : Term.term =
    match is1, is2 with
    | [], [] -> Term.mk_false
    | i1 :: is1, i2 :: is2 ->
      let i1, i2 = Term.mk_var i1, Term.mk_var i2 in
      Term.mk_or ~simpl:true
        (Term.mk_lt i1 i2)
        (Term.mk_and ~simpl:true (Term.mk_eq ~simpl:true i1 i2) (lt_lex is1 is2))
    | _ -> assert false
  in
      
  (* - Condition checking whether [(tau1, s1) < (tau2, s2)].
     - We use the lexicographic order [(Term.mk_lt, mt_map map_cnstrs)].
     - If [xocc1] and [xocc2] are the same occurrence, and if they have free
       variables on top of the action free variable (i.e. if they occur 
       below a binder), then we also consider self-collision between an 
       an occurrence and another occurrence at the same timestamp, but 
       earlier in the binder. *)
  let mk_xocc_lt
      (tau1 : Term.term) (xocc1 : XO.t)
      (tau2 : Term.term) (xocc2 : XO.t)
    : Term.term
    =
    (* collision between occurrences earlier in time *)
    let ts_lt =
      if lt_map map_cnstrs xocc1 xocc2 then
        Term.mk_leq tau1 tau2
      else
        Term.mk_lt tau1 tau2
    in

    (* same occurrence, appearing under a binder: self collision between
       [xocc2] and [xocc1] occurring earlier in the binder. *)
    let idx_lt =
      if xocc1.tag = xocc2.tag then
        let _, is1 = 
          List.takedrop (List.length xocc1.cnt.x_a_is) xocc1.cnt.x_occ.occ_vars 
        in
        let _, is2 = 
          List.takedrop (List.length xocc2.cnt.x_a_is) xocc2.cnt.x_occ.occ_vars 
        in
        Term.mk_and ~simpl:true (Term.mk_eq tau1 tau2) (lt_lex is1 is2)
      else Term.mk_false
    in

    Term.mk_or ~simpl:true ts_lt idx_lt
  in

  let mk_xocc_collision
      (tau1 : Term.term) (xocc1 : XO.t)
      (tau2 : Term.term) (xocc2 : XO.t)
    : Term.term
    = 
    (* condition stating that [x] is equal to a hash occurrence [xocc]. *)
    let occ_vars, occ_t = xocc1.cnt.x_occ.occ_cnt in
    Term.mk_ands ~simpl:true
      [ Term.mk_eq ~simpl:true tau_t (mk_occ_ts xocc1); (* timestamp equ. *)
        mk_xocc_lt tau1 xocc1 tau2 xocc2;               (* timestamp ord. *)
        Term.mk_eq ~simpl:true x_t occ_t;               (* hash content equ. *)
        Term.mk_eqs ~simpl:true key_is occ_vars;        (* hash key equ. *)
      ] 
  in

  let table, err_fs = 
    let ftype = Type.mk_ftype [] [] m_ty in
    Symbols.Function.declare
      table (L.mk_loc L._dummy "error") (ftype,Symbols.Abstract `Prefix)
  in
  let err_t = Term.mk_fun table err_fs [] in
    
  (* we rewrite [H(x,k)] at occurrence [s0] at time [tau0] into:
     [
       try find tau, occ s.t. (tau,s) < (tau0,s0) && x = s_{occ} 
       then n_{occ}@tau
       else n_occ0@tau0
     ] *)
  let rw_target (tau0_t : Term.term) (xocc0  : XO.t) =
    let cond =
      (* We check whether there exists [(tau,s)] such that:
         [(tau,s) < (tau0,s0) && x = s_x] *)
      Term.mk_ors
        (List.map (fun (xocc : XO.t) ->
             let _, xocc = XO.refresh xocc in
             Term.mk_exists ~simpl:true 
               xocc.cnt.x_occ.occ_vars
               (mk_xocc_collision tau_t xocc tau0_t xocc0)
           ) occs)
    in
    let t_else = mk_occ_term xocc0 in
    let t_then =
      List.fold_right (fun xocc t_then ->
          let _, xocc = XO.refresh xocc in
          let t_cond = mk_xocc_collision tau_t xocc tau0_t xocc0 in
          let t_occ = mk_occ_term xocc in
          Term.mk_find xocc.cnt.x_occ.occ_vars t_cond t_occ t_then
        ) occs err_t
      
    in
    Term.mk_find [tau] cond t_then t_else
  in

  (* - [ms] is the macro whose body we are rewritting at time [d] 
     - [pos] is the position at which we are trying to do the rewrite, 
       which is necessary to retrieve the associated fresh name. 
     - [bnd_vars] are the variable bound above [pos]. *)
  let mk_rw_rule
      (arg      : system_map_arg)
      (ms       : Symbols.macro)
      (bnd_vars : Vars.vars) 
      (pos      : Pos.pos) 
    : Rewrite.rw_rule option 
    =
    let hash_occ =
      List.find_opt (fun (xocc : XO.t) ->
          let found_descr = 
            match arg with
            | Macros.ADescr d -> xocc.cnt.x_a = d.name
            | Macros.AGlobal _ -> assert (Macros.is_global table ms); true
          in
          found_descr && 
          xocc.cnt.x_msymb = ms &&
          Sp.mem pos xocc.cnt.x_occ.occ_pos
        ) occs
    in
    match hash_occ with
    (* not an interesting position, no rewriting to do *)
    | None -> None

    (* interesting position, retrieve the associated occurrence *)
    | Some xocc ->
        let indices = 
          match arg with
          | Macros.ADescr d -> d.indices 
          | Macros.AGlobal a -> a.is
        in

      (* substitute [xocc] vars by the vars used during the rewriting *)
      let s = 
        List.map2 (fun i j -> 
            Term.ESubst (Term.mk_var i,Term.mk_var j)
          ) xocc.cnt.x_occ.occ_vars (indices @ bnd_vars)
      in
      let xocc = XO.subst s xocc in

      (* Time at which the term being rewritten in is evaluated. 
         - if we rewrite in the body of [output@A(i)] then [tau0] 
           is [A(i)]. 
         - if we rewrite in a global macro, we use the global macro
           dedicated timestamp variable. *)
      let tau0 = match arg with
        | Macros.ADescr d  -> Term.mk_action d.name (Term.mk_vars d.indices)
        | Macros.AGlobal a -> Term.mk_var a.ts 
      in
      
      let rule = Rewrite.{
          rw_tyvars = [];
          rw_system = SE.any;
          rw_vars   = Vars.Tag.local_vars (x :: is);
          rw_conds  = [];
          rw_rw     = (to_rw, rw_target tau0 xocc); }
      in
      Some rule
  in

  let fmap (arg : system_map_arg) (ms : Symbols.macro) (t : Term.term) 
    : Term.term 
    =
    let env = Vars.empty_env in
    (* only local variables, hence [env] should be useless here. *)

    (* To keep meaningful positions, we need to do the rewriting bottom-up.
       Indeed, this ensures that a rewriting does not modify the positions
       of the sub-terms above the position the rewriting occurs at. 

       We set [strict] to true, to make sure that we indeed rewrite at
       all necessary positions. *)
    Rewrite.high_rewrite ~mode:`BottomUp ~strict:true
      table env (old_system :> SE.t) (mk_rw_rule arg ms) t
  in

  let table, _new_system_e =
    clone_system_map table old_single_system sdecl.Decl.name fmap
  in 
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
      ~loc (TS.table s) (TS.vars s) (TS.system s) expand_context
      (TS.get_trace_hyps s)
      mult rw_erule (Local t)
  with
  | Local t, subs ->
    let subs =
      List.map (fun (sub_system, sub) -> 
          TS.set_goal_in_context sub_system sub s
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
    let subgs = List.map (fun x -> TS.set_goal x s) subgs in

    let t, subgs' = do_rewrite ~loc expand_context (rw_c, rule) s t in
    t, subgs @ subgs'

  | Rw_expand p_arg -> 
    let arg = TLT.p_rw_expand_arg s p_arg in
    let _, t = TLT.expand_term ~mode:expand_context arg s (Local t) in
    Equiv.any_to_reach t, []
  
  | Rw_expandall _ ->
    let _, t = TLT.expand_term ~mode:expand_context `Any s (Local t) in
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
    TS.Reduce.reduce_term ~expand_context param s t 

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
    let hyp_hap = Term.mk_happens ts in
    (* add hyp_hap as hypothesis, so it's available when do_rewrite tries to rewrite *)
    let (hyp_hap_id, s_hap) = TS.LocalHyps.add_i AnyName hyp_hap s in 

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
         let hyp_hap2 = Term.mk_ors ~simpl:true lex in
         let (hyp_hap2_id, s_hap2) = TS.LocalHyps.add_i AnyName hyp_hap2 s_hap in
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
                Vars.make `Approx (TS.vars gg) Type.Timestamp "t" (Vars.Tag.make Vars.Local)
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

  let subgs = List.map (fun s -> Goal.Trace s) !subgs in
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
  | PRFt (bnds, hash) -> global_prf_t   table sdecl bnds hash
  | CCA  (bnds, enc)  -> global_cca     table sdecl bnds  enc
  | Rewrite rw        -> global_rewrite table sdecl rw
