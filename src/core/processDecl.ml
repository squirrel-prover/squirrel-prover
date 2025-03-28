open Utils
open Ppenv

module L    = Location
module Args = TacticsArgs
module SE   = SystemExpr
module Mv   = Vars.Mv

type lsymb = Symbols.lsymb

(*------------------------------------------------------------------*)
(** {Error handling} *)

type error_i =
  | BadEquivForm
  | InvalidCtySpace of string list
  | DuplicateCty of string
  | NonDetOp
  | Failure of string

type dkind = KDecl | KLemma

type error =  L.t * dkind * error_i

let pp_error_i fmt = function
  | BadEquivForm ->
    Fmt.pf fmt "equivalence lemma ill-formed"

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
    | KDecl  -> Fmt.pf fmt "declaration"
    | KLemma -> Fmt.pf fmt "lemma declaration" in

  Fmt.pf fmt "%a@[<hov 2>%a failed: %a@]"
    pp_loc_err loc
    pp_k k
    pp_error_i e

exception Error of error

let error loc k e = raise (Error (loc,k,e))

(*------------------------------------------------------------------*)
(** {2 Declaration parsing} *)

(** [parse_state_decl n [(x1,s1);...;(xn;sn)] s t] declares
    a new state symbol of type [s1->...->sn->s]
    where [si] is [index] and [s] is [message]
    such that value of [s(t1,...,tn)] for init timestamp
    expands to [t\[x1:=t1,...,xn:=tn\]]. *)
let parse_state_decl
    (table : Symbols.table)
    ({ name; args = p_args; out_ty; init_body; } : Decl.state_macro_decl)
  =
  let ts_init = Term.mk_action Symbols.init_action [] in

  (* open a typing environment *)
  let ienv = Infer.mk_env () in
  
  let env = Env.init ~table () in
  let conv_env = Typing.{ env; cntxt = InProc ([], ts_init); } in

  let env, args = Typing.convert_bnds ~ienv ~mode:NoTags env p_args in
  let conv_env = { conv_env with env } in

  (* parse the macro type *)
  let out_ty = omap (Typing.convert_ty env) out_ty in

  let t, out_ty = Typing.convert ~ienv ?ty:out_ty conv_env init_body in

  (* close the typing environment and substitute *)
  let tsubst =
    match Infer.close env ienv with        
    | Infer.Closed subst -> subst

    | _ as e ->
      Typing.error (L.loc init_body) (Failure (Fmt.str "%a" Infer.pp_error_result e))
  in
  let t = Term.gsubst tsubst t in
  let args = List.map (Subst.subst_var tsubst) args in

  (* FIXME: generalize allowed types *)
  List.iter2 (fun v (_, pty) ->
      if not (Type.equal (Vars.ty v) Type.tindex) then
        Typing.error (L.loc pty) (BadPty [Type.tindex])
    ) args p_args;

  let data =
    Symbols.Macro
      (State (List.length p_args,out_ty, Macros.StateInit_data (args,t)))
  in
  let table, _ = Symbols.Macro.declare ~approx:false table name ~data in
  table

(*------------------------------------------------------------------*)
(** Parse an abstract or concrete operator declaration. *)
let parse_operator_decl table (decl : Decl.operator_decl) : Symbols.table =
    let ty_vars = List.map (fun l ->
        Type.mk_tvar (L.unloc l)
      ) decl.op_tyargs
    in

    (* open a typing environment *)
    let ienv = Infer.mk_env () in

    (* translate arguments *)
    let env = Env.init ~table ~ty_vars () in
    let env, subst, args =
      Typing.convert_ext_bnds
        ~ienv ~mode:(DefaultTag (Vars.Tag.make ~const:true Vars.Global)) 
        env decl.op_args
        (* assume global constant variables to properly check that the
           body represents a deterministic computations later
           (as constant => deterministic). *)
    in

    let out_ty = omap (Typing.convert_ty ~ienv env) decl.op_tyout in

    (* translate body *)
    let body, out_ty =
      match decl.op_body with
      | `Abstract ->
        if out_ty = None then 
          error (L.loc decl.op_name) KDecl (Failure "abstract operator must be typed");
        
        let out_ty = oget out_ty in
        let in_tys, out_ty = Type.decompose_funs out_ty in
        `Abstract in_tys, out_ty

      | `Concrete body ->
        let body, out_ty =
          Typing.convert ~ienv ?ty:out_ty { env; cntxt = InGoal; } body
        in
        let body = Term.subst subst body in
        `Concrete body, out_ty
    in

    (* check that the typing environment is closed *)
    let tsubst =
      match Infer.close env ienv with        
      | Infer.Closed subst -> subst

      | _ as e ->
        error (L.loc decl.op_name) KDecl (Failure (Fmt.str "%a" Infer.pp_error_result e))
    in
    let args = List.map (Subst.subst_var tsubst) args in
    let out_ty = Subst.subst_ty tsubst out_ty in
    (* substitue in [body] below, in the concrete case *)

    match body with
    | `Abstract in_tys ->       (* abstract declaration *)
      let in_tys = List.map Vars.ty args @ in_tys in
      Typing.declare_abstract table
        ~ty_args:ty_vars ~in_tys ~out_ty
        decl.op_name decl.op_symb_type

    | `Concrete body ->         (* concrete declaration *)
      let body = Term.gsubst tsubst body in

      if not (HighTerm.is_deterministic env body) then
        error (L.loc decl.op_name) KDecl NonDetOp;

      let table, name =
       Symbols.Operator.reserve ~approx:false table decl.op_name
      in

      let op_data = Operator.{ name; ty_vars; args; out_ty; body; } in
      let ftype = Operator.concrete_ftype op_data in

      (* sanity checks on infix symbols *)
      let in_tys = List.length args in (* number of arguments *)
      Typing.check_fun_symb in_tys decl.op_name decl.op_symb_type;

      let data = 
        Symbols.OpData.Operator {def = Concrete (Operator.Val op_data); ftype; } 
      in
      let table = Symbols.Operator.define table ~data name in

      let ppe = default_ppe ~table () in
      Printer.prt `Result "%a" (Operator._pp_concrete_operator ppe) op_data;

      table

(*------------------------------------------------------------------*)
let parse_game_decl loc table (decl : Crypto.Parse.game_decl) =
  let g = Crypto.Parse.parse loc table decl in

  let ppe = default_ppe ~table ~dbg:false () in
  Printer.prt `Result "%a" (Crypto._pp_game ppe) g;

  let table, _ =
    Symbols.Game.declare ~approx:false
      table decl.Crypto.Parse.g_name ~data:(Crypto.Game g) 
  in
  table

(*------------------------------------------------------------------*)
let parse_namespace_cmd table (cmd : Decl.namespace_info) : Symbols.table =
  match cmd with
  | Decl.Enter n -> Symbols.namespace_enter table n
  | Decl.Exit  n -> Symbols.namespace_exit  table n
  | Decl.Open  n -> Symbols.namespace_open  table (Symbols.convert_npath n table)
  | Decl.Close n -> Symbols.namespace_close table (Symbols.convert_npath n table)

(*------------------------------------------------------------------*)
let parse_predicate_decl table (decl : Decl.predicate_decl) : Symbols.table =
    let name = L.unloc decl.pred_name in

    let ty_params = List.map (fun l ->
        Type.mk_tvar (L.unloc l)
      ) decl.pred_tyargs
    in

    (* open a typing environment *)
    let ienv = Infer.mk_env () in

    let env =
      let system = SE.{
          set  = var SE.Var.set;
          pair = Some (SE.to_pair (var SE.Var.pair)); }
      in
      Env.init ~system ~table ~ty_vars:ty_params ()
    in

    (* parse the system variables declared and build the
       system variables environment *)
    let env, se_params =
      Typing.convert_se_var_bnds env decl.pred_se_args
    in

    (* parse binders for multi-term variables *)
    let (se_info, env), multi_args =
      List.map_fold
        (fun (se_info,env) (se_v,bnds) ->
           let se_v : SE.t =
             let se_name = L.unloc se_v in

             let v = 
               match SE.lookup_string se_name env.Env.se_vars with
               | None -> error (L.loc se_v) KDecl (Failure "unknown system variable")
               | Some v -> v
             in
             
             SE.var v
           in
           let env, args = Typing.convert_bnds ~ienv ~mode:NoTags env bnds in
           let se_info = Mv.add_list (List.map (fun v -> v, se_v) args) se_info in
           (se_info, env), (se_v, args)
        ) (Mv.empty, env) decl.pred_multi_args
    in
    (* parse binders for simple variables *)
    let env, simpl_args =
      Typing.convert_bnds ~ienv ~mode:NoTags env decl.pred_simpl_args
    in

    let body =
      match decl.pred_body with
      | None -> Predicate.Abstract
      | Some b ->
        let b =
          Typing.convert_global_formula
            ~ienv ~system_info:se_info
            { env; cntxt = InGoal; } b
        in
        Predicate.Concrete b
    in

    (* close the typing environment and substitute *)
    let tsubst =
      match Infer.close env ienv with        
      | Infer.Closed subst -> subst

      | _ as e ->
        let loc =
          match decl.pred_body with Some b -> L.loc b | None -> L.loc decl.pred_name
        in
        error loc KDecl (Failure (Fmt.str "%a" Infer.pp_error_result e))
    in
    
    let multi_args =
      List.map (fun (info, args) ->
          info, List.map (Subst.subst_var tsubst) args
        ) multi_args
    in
    let simpl_args = List.map (Subst.subst_var tsubst) simpl_args in
    let body = Predicate.gsubst_body tsubst body in

    let args = Predicate.{ multi = multi_args; simple = simpl_args; } in
    let data = Predicate.mk ~name ~se_params ~ty_params ~args ~body in

    (* sanity checks on infix symbols *)
    let in_tys =
      List.fold_left
        (fun in_tys (_, args) -> in_tys + List.length args)
        (List.length simpl_args) multi_args
    in
    Typing.check_fun_symb in_tys decl.pred_name decl.pred_symb_type;

    let table, _ =
      Symbols.Predicate.declare ~approx:false
        table decl.pred_name
        ~data:(Predicate.Predicate data)
    in

    let ppe = default_ppe ~table () in
    Printer.prt `Result "@[<v 2>new predicate:@;%a@;@]"
      (Predicate._pp ppe) data;

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

      let ty = Typing.convert_ty env cty.Decl.cty_ty in
      (sp, ty)
    ) ctys

(*------------------------------------------------------------------*)
let define_oracle_tag_formula (h : lsymb) table (fm : Typing.term) :
  Symbols.table =
  let env = Env.init ~table () in
  let conv_env = Typing.{ env; cntxt = InGoal; } in
  let form, _ = Typing.convert conv_env ~ty:Type.tboolean fm in
    match form with
     | Term.Quant (ForAll, [uvarm; uvarkey], _) ->
       begin
         match Vars.ty uvarm,Vars.ty uvarkey with
         | Type.(Message, Message) ->
           Oracle.add_oracle (h,form) table
         | _ ->
           ProverLib.error (L.loc fm)
             "The tag formula must be of the form forall
             (m:message,sk:message)"
       end

     | _ ->
       ProverLib.error (L.loc fm)
         "The tag formula must be of the form forall
         (m:message,sk:message)"

(*------------------------------------------------------------------*)
(** {2 Declaration processing} *)


let declare table decl : Symbols.table * Goal.t list =
  match L.unloc decl with
  | Decl.Decl_channel s -> Channel.declare table s, []

  | Decl.Decl_process { id; projs; args; proc} ->
    Process.declare table ~id ~args ~projs proc, []

  | Decl.Decl_action a ->
    let table, symb = Symbols.Action.reserve ~approx:false table a.a_name in
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
    let projs = Typing.parse_projs sdecl.sprojs in
    let exec_model = 
      match sdecl.system_option with
      | None 
      | Some { pl_desc = "classic"     } -> Action.Classic
      | Some { pl_desc = "postquantum" } -> Action.PostQuantum
      | Some l -> error (L.loc l) KDecl (Failure "unknown system option")
    in
    Process.declare_system table exec_model sdecl.sname projs sdecl.sprocess, []

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
     Typing.declare_dh table h ?group_ty ?exp_ty g ex om, []

  | Decl.Decl_hash (n, tagi, ctys) ->
    let table = match tagi with
      | Some t -> define_oracle_tag_formula n table t
      | None -> table in

    let ctys = parse_ctys table ctys ["m"; "h"; "k"] in
    let m_ty = List.assoc_opt  "m" ctys
    and h_ty = List.assoc_opt  "h" ctys
    and k_ty  = List.assoc_opt "k" ctys in

    Typing.declare_hash table ?m_ty ?h_ty ?k_ty n, []

  | Decl.Decl_aenc (enc, dec, pk, ctys) ->
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "r"; "sk"; "pk"] in
    let ptxt_ty = List.assoc_opt "ptxt" ctys
    and ctxt_ty = List.assoc_opt "ctxt" ctys
    and rnd_ty  = List.assoc_opt "r"    ctys
    and sk_ty   = List.assoc_opt "sk"   ctys
    and pk_ty   = List.assoc_opt "pk"   ctys in

    Typing.declare_aenc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?sk_ty ?pk_ty enc dec pk, []

  | Decl.Decl_senc (senc, sdec, ctys) ->
    let ctys = parse_ctys table ctys ["ptxt"; "ctxt"; "r"; "k"] in
    let ptxt_ty = List.assoc_opt "ptxt" ctys
    and ctxt_ty = List.assoc_opt "ctxt" ctys
    and rnd_ty  = List.assoc_opt "r"    ctys
    and k_ty    = List.assoc_opt "k"    ctys in

    Typing.declare_senc table ?ptxt_ty ?ctxt_ty ?rnd_ty ?k_ty senc sdec, []

  | Decl.Decl_name (s, p_ty) ->
    let env = Env.init ~table () in

    let p_args_tys, p_out_ty =
      match p_ty with
      | { pl_desc =
            Typing.P_fun (
              { pl_desc = Typing.P_tuple p_args_ty},
              p_out_ty
            )
        } ->
        p_args_ty, p_out_ty

      | { pl_desc = Typing.P_fun (p_arg_ty, p_out_ty)} ->
        [p_arg_ty], p_out_ty

      | _ -> [], p_ty
    in

    let args_tys = List.map (Typing.convert_ty env) p_args_tys in
    let out_ty = Typing.convert_ty env p_out_ty in

    if List.length (fst (Type.decompose_funs out_ty)) >= 1 then
      begin
        let str_warning =
          Fmt.str "@[<v>name %s samples functions of type@;\
                  \  @[%a@]@;\
                   maybe you wanted to use a non-curryfied type instead?"
            (L.unloc s) Type.pp out_ty
        in
        Printer.prt `Warning "%s" str_warning
      end;
    
    let n_fty = Type.mk_ftype_tuple [] args_tys out_ty in

    List.iter2 (fun ty pty ->
        (* necessary to ensure that a term semantics is always a random variables
           (indeed, this guarantees that the set of tapes is finite, and can be
           equipped with the discrete sigma-algebra and the uniform distribution) *)
        if not (Symbols.TyInfo.is_finite table ty) then
          error (L.loc pty) KDecl (Failure "name can only be index by finite types")
      ) args_tys p_args_tys;

    let table, n =
      let data = Symbols.Name Symbols.{ n_fty } in
      Symbols.Name.declare ~approx:false table s ~data
    in
    Process.add_namelength_axiom table n n_fty, []

  | Decl.Decl_state decl ->
    parse_state_decl table decl, []

  | Decl.Decl_senc_w_join_hash (senc, sdec, h) ->
    Typing.declare_senc_joint_with_hash table senc sdec h, []

  | Decl.Decl_sign (sign, checksign, pk, tagi, ctys) ->
    let table = match tagi with
      | Some t -> define_oracle_tag_formula sign table t
      | None -> table in

    let ctys = parse_ctys table ctys ["m"; "sig"; "sk"; "pk"] in
    let m_ty     = List.assoc_opt "m"     ctys
    and sig_ty   = List.assoc_opt "sig"   ctys
    and sk_ty    = List.assoc_opt "sk"    ctys
    and pk_ty    = List.assoc_opt "pk"    ctys in

    Typing.declare_signature table
      ?m_ty ?sig_ty ?sk_ty ?pk_ty sign checksign pk,
    []

  | Decl.Decl_operator  decl -> parse_operator_decl table decl,  []
  | Decl.Decl_predicate decl -> parse_predicate_decl table decl, []

  | Decl.Decl_bty bty_decl ->
    let table, _ =
      let ty_infos = List.map Symbols.TyInfo.parse bty_decl.bty_infos in
      Symbols.BType.declare ~approx:false
        table
        bty_decl.bty_name
        ~data:(Symbols.TyInfo.Type ty_infos)
    in
    table, []

  | Decl.Decl_game game -> parse_game_decl (L.loc decl) table game, []

  | Decl.Tactic (id,ast) ->
    ProverTactics.register_macro (L.unloc id) ast ;
    table, []

  | Decl.Namespace_cmd cmd -> parse_namespace_cmd table cmd, []

let declare_list table decls =
  let table, subgs =
    List.map_fold (fun table d -> declare table d) table decls
  in
  table, List.flatten subgs

(*------------------------------------------------------------------*)
(** Check that [lem] applies to an unconstrained system variable [v]. *)
let local_stmt_valid_in_any_system (lem : Goal.local_statement) =
  match (lem.system.set :> SE.exposed).cnt with
  | Var v -> 
    let infos = List.assoc v lem.params.se_vars in
    infos = []
  | _ -> false

(*------------------------------------------------------------------*)
(** {3 Hints } *)

(*------------------------------------------------------------------*)
let add_hint_rewrite table (s : Symbols.p_path) =
  let lem = Lemma.find_stmt_local s table in
  let bound = lem.formula.bound in

  (* TODO: concrete: only support exact hint rather *)
  if bound <> None then
    Tactics.hard_failure ~loc:(L.loc (snd s))
      (Failure "rewrite hints must be asymptotic or exact");

  assert (lem.system.pair = None;); (* as we only forward [system.set] below *)

  Hint.add_hint_rewrite s lem.params lem.system.set lem.Goal.formula.formula table

(*------------------------------------------------------------------*)
let add_hint_smt table (s : Symbols.p_path) =
  let lem = Lemma.find_stmt_local s table in
  let bound = lem.formula.bound in

  (* TODO: concrete: only support exact hint rather *)
  if bound <> None || bound <> Some (Library.Real.mk_zero table) then
    Tactics.hard_failure ~loc:(L.loc (snd s))
      (Failure "smt hints must be asymptotic or exact");

  if not (local_stmt_valid_in_any_system lem) then
    Tactics.hard_failure ~loc:(Symbols.p_path_loc s)
      (Failure "smt hints must apply to any system");

  if lem.params.se_vars <> [] then
    Tactics.hard_failure ~loc:(Symbols.p_path_loc s)
      (Failure "smt hints do not support system variables");

  Hint.add_hint_smt lem.Goal.formula.formula table

(*------------------------------------------------------------------*)
let deduction_hint_of_global_formula
    table loc (params : Params.t) (form : Equiv.form) : Hint.deduce_rule
  =
  let open Equiv in
  let failed error =
    Typing.error loc (Failure ("ill-formed deduction hint: " ^ error))
  in

  let uded = Library.Deduction.uniform_deduction table in

  let p = 
    match form with
    | Atom (Pred p) when p.psymb = uded -> p
    | _ -> failed ("must be a " ^ Symbols.path_to_string uded ^ " atom")
  in

  let system = as_seq1 p.se_args in

  (* [p.ty_args] starts by the type of the uniform argument to both
     [left] and [right]. 
     We extract it in [ty_args], possibly decomposing tuple arguments. *)
  let ty_arg = (List.hd p.ty_args) in
  let ty_args = Type.decompose_tuple ty_arg  in

  (* Get [left] and [right]. *)
  let left, right = 
    let _, pred_args = as_seq1 p.multi_args in
    as_seq2 pred_args
  in

  (* Apply them to the uniform arguments of the deduction property. *)
  let args = List.map (fun ty -> Vars.make_fresh ty "x") ty_args in
  let term_args = List.map Term.mk_var args in
  let left  = Term.mk_app ~simpl:true left  term_args in
  let right = Term.mk_app ~simpl:true right term_args in

  (* Try to decompose [right] as [(right | ∀ vars : cond)], which is
     sugar for [λ vars. (if cond then right else witness)]. *)
  let vars, right = 
    let vars, right = Term.decompose_fun right in
    let vars, subst = Term.refresh_vars vars in
    vars, Term.subst subst right     
  in
  let right, cond = 
    match Term.destr_app ~fs:Symbols.fs_ite ~arity:3 right with
    | Some [cond; t_then; Term.Fun (w, _)] 
      when   ( w = Library.Prelude.fs_witness && 
               not (Type.equal (Term.ty t_then) Type.tmessage) ) 
           || w = Symbols.fs_zero -> t_then, cond
    | _ -> right, Term.mk_true
  in

  { params; system; args; left; vars; right; cond; }

let add_hint_deduce table (s : Symbols.p_path) = 
  let lem = Lemma.find_stmt_global s table in

  let name = Symbols.p_path_to_string ~sep:"_" s in
  let rule = 
    deduction_hint_of_global_formula 
      table (Symbols.p_path_loc s) lem.params lem.formula
  in
  let h = Hint.{ name; cnt = rule; info = (); } in

  let ppe = default_ppe ~table () in
  Printer.prt `Result "@[<v 2>New deduction hint %a@]" 
    (Hint._pp_deduce_hint ppe) h;

  Hint.add_hint_deduce h table


(*------------------------------------------------------------------*)
let add_hint (table : Symbols.table) (h : Hint.p_hint) : Symbols.table =
  match h with
  | Hint.Hint_rewrite id -> add_hint_rewrite table id 
  | Hint.Hint_smt     id -> add_hint_smt     table id 
  | Hint.Hint_deduce  id -> add_hint_deduce  table id 
