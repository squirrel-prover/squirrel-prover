open Utils

module L    = Location
module Args = TacticsArgs
module SE   = SystemExpr

type lsymb = Theory.lsymb

(*------------------------------------------------------------------*)
(** {Error handling} *)

type error_i =
  | BadEquivForm
  | InvalidCtySpace of string list
  | DuplicateCty of string
  | NonDetOp
  | Failure of string

type dkind = KDecl | KGoal

type error =  L.t * dkind * error_i

let pp_error_i fmt = function
  | BadEquivForm ->
    Fmt.pf fmt "equivalence goal ill-formed"

  | InvalidCtySpace kws ->
    Fmt.pf fmt "invalid space@ (allowed: @[<hov 2>%a@])"
      (Fmt.list ~sep:Fmt.comma Fmt.string) kws

  | DuplicateCty s -> Fmt.pf fmt "duplicated entry %s" s

  | NonDetOp ->
    Fmt.pf fmt "an operator body cannot contain probabilistic computations"

  | Failure s ->
    Fmt.pf fmt "%s" s
      
let pp_error pp_loc_err fmt (loc,k,e) =
  let pp_k fmt = function
    | KDecl -> Fmt.pf fmt "declaration"
    | KGoal -> Fmt.pf fmt "goal declaration" in

  Fmt.pf fmt "%a@[<hov 2>%a failed: %a@]"
    pp_loc_err loc
    pp_k k
    pp_error_i e

exception Error of error

let error loc k e = raise (Error (loc,k,e))

(*------------------------------------------------------------------*)
(** {2 Declaration parsing} *)

let rec split_ty (ty : Theory.p_ty) : Theory.p_ty list =
  match L.unloc ty with
  | Theory.P_fun (t1, t2) -> t1 :: split_ty t2
  | _ -> [ty]
         
let parse_abstract_decl table (decl : Decl.abstract_decl) =
  let in_tys, out_ty =
    let tys = split_ty decl.abs_tys in
    List.takedrop (List.length tys - 1) tys
  in
  let p_out_ty = as_seq1 out_ty in

  let ty_args = List.map (fun l ->
      Type.mk_tvar (L.unloc l)
    ) decl.ty_args
  in

  let env = Env.init ~table ~ty_vars:ty_args () in
  let in_tys = List.map (Theory.convert_ty env) in_tys in

  let out_ty = Theory.convert_ty env p_out_ty in

  Theory.declare_abstract table
    ~ty_args ~in_tys ~out_ty
    decl.name decl.symb_type

(*------------------------------------------------------------------*)
let parse_operator_decl table (decl : Decl.operator_decl) =
    let name = L.unloc decl.op_name in

    let ty_vars = List.map (fun l ->
        Type.mk_tvar (L.unloc l)
      ) decl.op_tyargs
    in

    (* open a typing environment *)
    let ty_env = Type.Infer.mk_env () in

    let env = Env.init ~table ~ty_vars () in
    let env, subst, args =
      Theory.convert_ext_bnds ~ty_env (Vars.Tag.make ~const:true Vars.Global) env decl.op_args
      (* assume global constant variables to properly check that the
         body represents a deterministic computations later
         (as constant => deterministic). *)
    in

    let out_ty = omap (Theory.convert_ty ~ty_env env) decl.op_tyout in

    let body, out_ty = 
      Theory.convert ~ty_env ?ty:out_ty { env; cntxt = InGoal } decl.op_body 
    in
    let body = Term.subst subst body in

    (* check that the typing environment is closed *)
    if not (Type.Infer.is_closed ty_env) then 
      error (L.loc decl.op_body) KDecl (Failure "some types could not be inferred");

    (* close the typing environment and substitute *)
    let tsubst = Type.Infer.close ty_env in
    let args = List.map (Vars.tsubst tsubst) args in
    let out_ty = Type.tsubst tsubst out_ty in
    let body = Term.tsubst tsubst body in

    if not (HighTerm.is_deterministic env body) then
      error (L.loc decl.op_body) KDecl NonDetOp;

    let data = Operator.mk ~name ~ty_vars ~args ~out_ty ~body in
    let ftype = Operator.ftype data in

    let in_tys = List.map Vars.ty args in

    (* sanity checks on infix symbols *)
    Theory.check_fun_symb table in_tys decl.op_name decl.op_symb_type;
    
    let table, _ = 
      Symbols.Function.declare_exact 
        table decl.op_name
        ~data:(Operator.Operator data)
        (ftype, Symbols.Operator)
    in

    Printer.prt `Result "@[<v 2>new operator:@;%a@]" 
      Operator.pp_operator data;

    table

(*------------------------------------------------------------------*)
(** Parse additional type information for procedure declarations 
    (enc, dec, hash, ...) *)
let parse_ctys table (ctys : Decl.c_tys) (kws : string list) =
  (* check for duplicate *)
  let _ : string list = List.fold_left (fun acc cty ->
      let sp = L.unloc cty.Decl.cty_space in
      if List.mem sp acc then
        error (L.loc cty.Decl.cty_space) KDecl (DuplicateCty sp);
      sp :: acc
    ) [] ctys in

  let env = Env.init ~table () in

  (* check that we only use allowed keyword *)
  List.map (fun cty ->
      let sp = L.unloc cty.Decl.cty_space in
      if not (List.mem sp kws) then
        error (L.loc cty.Decl.cty_space) KDecl (InvalidCtySpace kws);

      let ty = Theory.convert_ty env cty.Decl.cty_ty in
      (sp, ty)
    ) ctys

let parse_projs (p_projs : lsymb list option) : Term.projs =
  omap_dflt
    [Term.left_proj; Term.right_proj]
    (List.map (Term.proj_from_string -| L.unloc))
    p_projs

(*------------------------------------------------------------------*)
let define_oracle_tag_formula table (h : lsymb) (fm : Theory.term) =
  let env = Env.init ~table () in
  let conv_env = Theory.{ env; cntxt = InGoal; } in
  let form, _ = Theory.convert conv_env ~ty:Type.Boolean fm in
    match form with
     | Term.Quant (ForAll, [uvarm; uvarkey], _) ->
       begin
         match Vars.ty uvarm,Vars.ty uvarkey with
         | Type.(Message, Message) ->
           ProverLib.add_option (Oracle_for_symbol (L.unloc h), Oracle_formula form)
         | _ ->
           ProverLib.error (L.loc fm) 
             "The tag formula must be of the form forall (m:message,sk:message)"
       end

     | _ -> 
       ProverLib.error (L.loc fm)
         "The tag formula must be of the form forall (m:message,sk:message)"


(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)


let declare table decl : Symbols.table * Goal.t list = 
  match L.unloc decl with
  | Decl.Decl_channel s -> Channel.declare table s, []

  | Decl.Decl_process { id; projs; args; proc} ->
    let env = Env.init ~table () in
    let args = List.map (fun (x,t) ->
        L.unloc x, Theory.convert_ty env t
      ) args
    in
    let projs = parse_projs projs in
    
    Process.declare table id args projs proc, []

  | Decl.Decl_action a ->
    let table, symb = Symbols.Action.reserve_exact table a.a_name in
    Action.declare_symbol table symb a.a_arity, []

  | Decl.Decl_axiom pgoal ->
    let pgoal =
      match pgoal.Goal.Parsed.name with
      | Some _ -> pgoal
      | None ->
        (* XXX is this dependence to ProverLib necessary ? *)
        { pgoal with Goal.Parsed.name = Some (ProverLib.unnamed_goal ()) }
    in
    let loc = L.loc (oget pgoal.Goal.Parsed.name) in
    let gc,_ = Goal.make table pgoal in
    Lemma.add_lemma ~loc `Axiom gc table, []

  | Decl.Decl_system sdecl ->
    let projs = parse_projs sdecl.sprojs in
    Process.declare_system table sdecl.sname projs sdecl.sprocess, []

  | Decl.Decl_system_modifier sdecl ->
    let new_lemma, proof_obls, table =
      SystemModifiers.declare_system table sdecl 
    in
    let table = omap_dflt table (Lemma.add_lemma `Lemma ^~ table) new_lemma in
    table, proof_obls

  | Decl.Decl_dh (h, g, ex, om, ctys) ->
     let ctys =
       parse_ctys table ctys ["group"; "exponents"]
     in
     let group_ty = List.assoc_opt "group"     ctys
     and exp_ty   = List.assoc_opt "exponents" ctys in
     Theory.declare_dh table h ?group_ty ?exp_ty g ex om, []

  | Decl.Decl_hash (n, tagi, ctys) ->
    let () = Utils.oiter (define_oracle_tag_formula table n) tagi in

    let ctys = parse_ctys table ctys ["m"; "h"; "k"] in
    let m_ty = List.assoc_opt  "m" ctys
    and h_ty = List.assoc_opt  "h" ctys
    and k_ty  = List.assoc_opt "k" ctys in

    Theory.declare_hash table ?m_ty ?h_ty ?k_ty n, []

  | Decl.Decl_aenc (enc, dec, pk, ctys) ->
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "rnd"; "sk"; "pk"] in
    let ptxt_ty = List.assoc_opt "ptxt" ctys
    and ctxt_ty = List.assoc_opt "ctxt" ctys
    and rnd_ty  = List.assoc_opt "rnd"  ctys
    and sk_ty   = List.assoc_opt "sk"   ctys
    and pk_ty   = List.assoc_opt "pk"   ctys in

    Theory.declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk, []

  | Decl.Decl_senc (senc, sdec, ctys) ->
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "rnd"; "k"] in
    let ptxt_ty = List.assoc_opt "ptxt" ctys
    and ctxt_ty = List.assoc_opt "ctxt" ctys
    and rnd_ty  = List.assoc_opt "rnd"  ctys
    and k_ty    = List.assoc_opt  "k"   ctys in

    Theory.declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty senc sdec, []

  | Decl.Decl_name (s, p_args_ty, p_out_ty) ->
    let env = Env.init ~table () in

    let p_args_tys = match p_args_ty with
      | Some { pl_desc = Theory.P_tuple p_tys} -> p_tys
      | Some p_ty -> [p_ty]
      | None -> []
    in

    let args_tys = List.map (Theory.convert_ty env) p_args_tys in
    let out_ty = Theory.convert_ty env p_out_ty in
    
    let n_fty = Type.mk_ftype_tuple [] args_tys out_ty in

    List.iter2 (fun ty pty ->
        (* necessary to ensure that a term semantics is always a random variables 
           (indeed, this guarantees that the set of tapes is finite, and can be 
           equipped with the discrete sigma-algebra and the uniform distribution) *)
        if not (Symbols.TyInfo.is_finite table ty) then
          error (L.loc pty) KDecl (Failure "name can only be index by finite types")
      ) args_tys p_args_tys;
    
    let table = Theory.declare_name table s Symbols.{ n_fty } in
    Process.add_namelength_axiom table s n_fty, []

  | Decl.Decl_state { name; args; out_ty; init_body; } ->
    Theory.declare_state table name args out_ty init_body, []

  | Decl.Decl_senc_w_join_hash (senc, sdec, h) ->
    Theory.declare_senc_joint_with_hash table senc sdec h, []

  | Decl.Decl_sign (sign, checksign, pk, tagi, ctys) ->
    let () = Utils.oiter (define_oracle_tag_formula table sign) tagi in

    let ctys = parse_ctys table ctys ["m"; "sig"; "sk"; "pk"] in
    let m_ty     = List.assoc_opt "m"     ctys
    and sig_ty   = List.assoc_opt "sig"   ctys
    and sk_ty    = List.assoc_opt "sk"    ctys
    and pk_ty    = List.assoc_opt "pk"    ctys in

    Theory.declare_signature table
      ?m_ty ?sig_ty ?sk_ty ?pk_ty sign checksign pk,
    []

  | Decl.Decl_abstract decl -> parse_abstract_decl table decl, []
  | Decl.Decl_operator decl -> parse_operator_decl table decl, []

  | Decl.Decl_bty bty_decl ->
    let table, _ =
      Symbols.BType.declare_exact
        table
        bty_decl.bty_name
        (List.map Symbols.TyInfo.parse bty_decl.bty_infos)
    in
    table, []

let declare_list table decls =
  let table, subgs = 
    List.map_fold (fun table d -> declare table d) table decls
  in
  table, List.flatten subgs

(*------------------------------------------------------------------*)
let add_hint_rewrite table (s : lsymb) db =
  let lem = Lemma.find_stmt_reach s table in
  
  if not (SE.subset table SE.any lem.system.set) then
    Tactics.hard_failure ~loc:(L.loc s)
      (Failure "rewrite hints must apply to any system");

  Hint.add_hint_rewrite s lem.Goal.ty_vars lem.Goal.formula db

let add_hint_smt table (s : lsymb) db =
  let lem = Lemma.find_stmt_reach s table in

  if not (SE.subset table SE.any lem.system.set) then
    Tactics.hard_failure ~loc:(L.loc s)
      (Failure "rewrite hints must apply to any system");

  Hint.add_hint_smt lem.Goal.formula db
