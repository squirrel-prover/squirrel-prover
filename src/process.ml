open Utils

module L = Location

let dum : L.t = L._dummy

(** We use dummy locations for intermediary term we build, which do not come
    from the user. *)
let mk_dum (v : 'a) : 'a L.located = L.mk_loc dum v

(*------------------------------------------------------------------*)
type proc_ty = (string * Type.ty) list

let pp_proc_ty =
  let pp_el fmt (s,e) = Fmt.pf fmt "(%s : %a)" s Type.pp e in
  (Fmt.list pp_el)

(*------------------------------------------------------------------*)
type lsymb = Theory.lsymb

type term = Theory.term

(*------------------------------------------------------------------*)
type process_i =
  | Null
  | New      of lsymb * Theory.p_ty * process
  | In       of Channel.p_channel * lsymb * process
  | Out      of Channel.p_channel * term * process
  | Parallel of process * process
  | Set      of lsymb * lsymb list * term * process
  | Let      of lsymb * term * Theory.p_ty option * process
  | Repl     of lsymb * process
  | Exists   of lsymb list * term * process * process
  | Apply    of lsymb * term list
  | Alias    of process * lsymb

and process = process_i L.located

(*------------------------------------------------------------------*)
let rec pp_process ppf process =
  let open Fmt in
  match L.unloc process with
  | Null -> Printer.kws `ProcessName ppf "null"

  | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (Printer.kws `ProcessName) (L.unloc s)
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") Theory.pp) l

  | Alias (p,a) ->
      pf ppf "@[%s:@ %a@]"
        (L.unloc a)
        pp_process p

  | Repl (s, p) ->
    pf ppf "@[<hov 2>!_%s@ @[%a@]@]"
      (L.unloc s) pp_process p

  | Set (s, indices, t, p) ->
    pf ppf "@[<hov>%s%a %a@ %a;@ @[%a@]@]"
      (L.unloc s)
      (Utils.pp_list Fmt.string) (L.unlocs indices)
      (Printer.kws `ProcessKeyword) ":="
      Theory.pp t
      pp_process p

  | New (s, t, p) when L.unloc t = Theory.P_message ->
    pf ppf "@[<hov>%a %a;@ @[%a@]@]"
      (Printer.kws `ProcessKeyword) "new"
      (Printer.kws `ProcessVariable) (L.unloc s)
      pp_process p

  | New (s, t, p) ->
    pf ppf "@[<hov>%a %a : %a;@ @[%a@]@]"
      (Printer.kws `ProcessKeyword) "new"
      (Printer.kws `ProcessVariable) (L.unloc s)
      Theory.pp_p_ty t
      pp_process p

  | In (c, s, p) ->
    pf ppf "@[<hov>%a(%a,@,%a);@ %a@]"
      (Printer.kws `ProcessInOut) "in"
      (Printer.kws `ProcessChannel) (L.unloc c)
      (Printer.kws `ProcessVariable) (L.unloc s)
      pp_process p

  | Out (c, t, p) ->
    pf ppf "@[<hov>%a(%a,@,%a);@ %a@]"
      (Printer.kws `ProcessInOut) "out"
      (Printer.kws `ProcessChannel) (L.unloc c)
      Theory.pp t
      pp_process p

  | Parallel (p1, p2) ->
    pf ppf "@[<hv>@[(%a)@] |@ @[(%a)@]@]"
      pp_process p1
      pp_process p2

  | Let (s, t, tyo, p) ->
    let pp_tyo fmt = function
      | None -> ()
      | Some ty -> Fmt.pf fmt " : %a" Theory.pp_p_ty ty
    in
    
    pf ppf "@[<v>@[<2>%a %a%a =@ @[%a@] %a@]@ %a@]"
      (Printer.kws `ProcessKeyword) "let"
      (Printer.kws `ProcessVariable) (L.unloc s)
      pp_tyo tyo
      Theory.pp t
      (Printer.kws `ProcessKeyword) "in"
      pp_process p

  | Exists (ss, f, p1, p2) ->
    if ss = [] then
      pf ppf "@[<hov>%a %a %a@;<1 2>%a"
        (Printer.kws `ProcessCondition) "if"
        Theory.pp f
        (Printer.kws `ProcessCondition) "then"
        pp_process p1
    else
      pf ppf "@[<hov>%a %a %a %a %a@;<1 2>%a"
        (Printer.kws `ProcessCondition) "find"
        (Utils.pp_list Fmt.string) (L.unlocs ss)
        (Printer.kws `ProcessCondition) "such that"
        Theory.pp f
        (Printer.kws `ProcessCondition) "in"
        pp_process p1 ;
    if L.unloc p2 <> Null then
      pf ppf "@ %a@;<1 2>%a@]"
      (Printer.kws `ProcessCondition) "else"
      pp_process p2
    else
      pf ppf "@]"

(*------------------------------------------------------------------*)
let is_out_i = function Out _ -> true | _ -> false
let is_out p = is_out_i (L.unloc p)

(*------------------------------------------------------------------*)
type error_i =
  | Arity_error of string * int * int
  | StrictAliasError of string
  | DuplicatedUpdate of string
  | Freetyunivar
  | ProjsMismatch    of Term.projs * Term.projs

type error = L.t * error_i

let pp_error_i fmt = function
  | StrictAliasError s -> Fmt.pf fmt "strict alias error: %s" s

  | Arity_error (s,i,j) -> 
    Fmt.pf fmt "process %s used with arity %i, but \
                defined with arity %i" s i j

  | DuplicatedUpdate s -> 
    Fmt.pf fmt "state %s can only be updated once in an action" s

  | Freetyunivar -> 
    Fmt.pf fmt "some type variable(s) could not be instantiated"

  | ProjsMismatch (ps1, ps2) ->
    Fmt.pf fmt "projections mismatch: @[%a@] ≠ @[%a@]"
      Term.pp_projs ps1
      Term.pp_projs ps2

let pp_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aProcess error: @[%a@]."
    pp_loc_err loc
    pp_error_i e

exception Error of error

let error loc e = raise (Error (loc,e))

(*------------------------------------------------------------------*)
(** We extend the symbols data with (bi)-processus descriptions and
    their types. *)
type Symbols.data += Process_data of proc_ty * Term.projs * process

let declare_nocheck table name (kind : proc_ty) projs proc =
    let data = Process_data (kind,projs,proc) in
    let def = () in
    Symbols.Process.declare_exact table name ~data def

let find_process table pname =
  match Symbols.Process.get_all pname table with
  | (), Process_data (kind, projs, proc) -> kind,projs,proc
  | _ -> assert false
  (* The data associated to a process must be a [Process_data _]. *)

let find_process_lsymb table (lsymb : lsymb) =
  let name = Symbols.Process.of_lsymb lsymb table in
  find_process table name

let check_channel table (s : lsymb) =
  ignore(Channel.of_lsymb s table : Channel.t)

(*------------------------------------------------------------------*)
(** Type checking for processes *)
let check_proc (env : Env.t) (projs : Term.projs) (p : process) =
  let rec check_p (ty_env : Type.Infer.env) (env : Env.t) proc =
    let loc = L.loc proc in
    match L.unloc proc with
    | Null -> ()

    | New (x, ty, p) -> 
      let ty = Theory.convert_ty env ty in 
      let vars, _ = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      check_p ty_env { env with vars } p

    | In (c,x,p) -> 
      check_channel env.table c;

      (* FEATURE: subtypes*)
      let vars, _ = Vars.make_local `Shadow env.vars (Type.Message) (L.unloc x) in
      check_p ty_env { env with vars } p

    | Out (c,m,p)

    | Alias (L.{ pl_desc = Out (c,m,p) },_) ->
      check_channel env.table c;

      (* raise an error if we are in strict alias mode *)
      if is_out proc && (TConfig.strict_alias_mode env.table)
      then error loc (StrictAliasError "missing alias")
      else
        (* FEATURE: subtypes *)
        let () = 
          Theory.check env ~local:true ty_env projs m Type.tmessage 
        in
        check_p ty_env env p

    | Alias (p,_) -> check_p ty_env  env p

    | Set (s, l, m, p) ->
      let k = Theory.check_state env.table s (List.length l) in
      Theory.check env ~local:true ty_env projs m k ;
      List.iter (fun x ->
          Theory.check 
            env ~local:true ty_env projs (Theory.var_of_lsymb x) Type.tindex
        ) l ;
      check_p ty_env  env p

    | Parallel (p, q) -> check_p ty_env  env p ; check_p ty_env  env q

    | Let (x, t, ptyo, p) ->
      let ty : Type.ty = match ptyo with
        | None -> TUnivar (Type.Infer.mk_univar ty_env)
        | Some pty -> Theory.convert_ty env pty 
      in
      
      Theory.check env ~local:true ty_env projs t ty ;
      let vars, _ = Vars.make_local `Shadow env.vars ty (L.unloc x) in
      check_p ty_env { env with vars } p

    | Repl (x, p) -> 
      let vars, _ = Vars.make_local `Shadow env.vars Type.Index (L.unloc x) in
      check_p ty_env { env with vars } p

    | Exists (vs, test, p, q) ->
      check_p ty_env  env q ;
      let vars =
        List.fold_left (fun vars x ->
            let vars, _ = Vars.make_local `Shadow vars Type.Index (L.unloc x) in
            vars
          ) env.vars vs 
      in
      let env = { env with vars } in
      Theory.check env ~local:true ty_env projs test Type.tboolean ;
      check_p ty_env  env p

    | Apply (id, ts) ->
      let kind, projs', _ = find_process_lsymb env.table id in

      if projs <> projs' then
        error (L.loc proc) (ProjsMismatch (projs, projs'));

      if List.length kind <> List.length ts then
        error loc (Arity_error (L.unloc id,
                                   List.length ts,
                                   List.length kind));
      List.iter2
        (fun (_, k) t -> Theory.check env ~local:true ty_env projs t k)
        kind ts
  in

  let ty_env = Type.Infer.mk_env () in

  check_p ty_env env p;

  if not (Type.Infer.is_closed ty_env) then
    error (L.loc p) Freetyunivar;

  ()


let declare
    (table : Symbols.table)
    (id : lsymb) (args : proc_ty) (projs : Term.projs)
    (proc : process)
  =
  let vars = 
    List.fold_left (fun vars (v, ty) ->
        let vars, _ = Vars.make_local `Shadow vars ty v in
        vars
      ) Vars.empty_env args 
  in
  let env = Env.init ~vars ~table () in

  (* type-check and declare *)
  check_proc env projs proc ;
  let table, _ = declare_nocheck env.table id args projs proc in
  table

(*------------------------------------------------------------------*)
(* Enable/disable debug messages by setting debug to debug_on/off. *)

let[@warning "-32"] debug_off fmt = Format.fprintf Printer.dummy_fmt fmt
let[@warning "-32"] debug_on fmt =
  Format.printf "[DEBUG] " ;
  Format.printf fmt

let debug = debug_off

let print_isubst isubst =
  debug "will print isubst@." ;
  List.iter
    (fun (s,th,v) -> debug "[%s,%a,%a]@." s Theory.pp_i th Vars.pp v)
    isubst

let print_msubst msubst =
  debug "will print msubst@." ;
  List.iter
    (fun (s,th,tm) -> debug "[%s,%a,%a]@." s Theory.pp_i th Term.pp tm)
    msubst

(*------------------------------------------------------------------*)
(* Type for data we store while parsing the process, needed to compute
 * the corresponding set of actions. *)
type p_env = {
  ty_env : Type.Infer.env;

  projs : Term.projs;
  (* valid projections for the process being parsed *)
  
  alias : lsymb ;
  (* current alias used for action names in the process *)

  indices : Vars.var list ;
  (* current list of bound indices (coming from Repl or Exists constructs) *)

  env : Env.t ;
  (* environment *)

  isubst : (string * Theory.term_i * Vars.var) list ;
  (* substitution for index variables (Repl, Exists, Apply)
   * mapping each variable from the original process (before refresh)
   * to the associated refreshed variables
   * as Theory.term and as a Vars.var suitable for use in Term.term *)

  msubst : (string * Theory.term_i * Term.term) list ;
  (* substitution for message variables (New, Let, In, Apply)
   * each variable from the original process (before refresh)
   * is mapped to the associated refreshed variable
   * as a Theory.term and as a Term.term
   * (the third component is also used to map input variables to
   * input macros) *)

  inputs : (Channel.t * Vars.var) list ;
  (* bound input variables *)

  (* RELATED TO THE CURRENT ACTION *)
  evars : Vars.var list ;
  (* variables bound by existential quantification *)

  action : Action.action_v ;
  (* the type [Action.action] describes the execution point in the protocol
     stored reversed *)

  facts : Term.term list ;
  (* list of formulas to create the condition term of the action *)

  updates : (lsymb * Vars.var list * Type.ty * Term.term) list ;
  (* list of updates performed in the action.
   * The type can be a type unification variables. *)

  globals : Symbols.macro list;
  (* list of global macros declared at [action] *)

}

let parse_proc (system_name : System.t) init_table init_projs proc =

  (* Initial env with special variables registered.
   * The special variables should never be visible to the user,
   * we prefix their names with $ to avoid conflicts with user names,
   * and also register special variables in the environment for extra
   * safety. *)
  let env_ts,ts,dummy_in =
    let env = Vars.empty_env in
    let env,ts = Vars.make_local `Shadow env Type.Timestamp "$ts" in
    let env,dummy_in = Vars.make_local `Shadow env Type.Message "$dummy" in
    env,ts,dummy_in
  in

  (* Update env.vars_env with a new variable of sort [sort] computed from
   * [name] *)
  let make_fresh param (penv : p_env) sort name =
    let vars,x = Vars.make_local param penv.env.vars sort name in
    { penv with env = { penv.env with vars }}, x
  in

  let create_subst (venv : Vars.env) isubst msubst =
    List.map (fun (x,_,tm) -> 
        let v, _ = as_seq1 (Vars.find venv x) in
        (* cannot have two variables with the same name since previous 
           definitions must have been shadowed *)
        Term.ESubst (Term.mk_var v, Term.mk_var tm)
      ) isubst
    @
    List.map (fun (x,_,tm) -> 
        let v, _ = as_seq1 (Vars.find venv x) in (* idem *)
        Term.ESubst (Term.mk_var v, tm)
      ) msubst
  in

  (* Convert a Theory.term to Term.term using the special sort
   * of substitution ([isubst] and [msubst]) maintained by the
   * parsing function.
   * The special timestamp variable [ts] is used. *)
  let conv_term 
      (penv  : p_env)
      (ts    : Term.term) 
      (t     : Theory.term)
      (ty    : Type.ty) 
    : Term.term 
    =
    let t, _ = 
      Theory.convert ~ty_env:penv.ty_env 
        { env = penv.env; cntxt = InProc (penv.projs,ts); } ~ty t 
    in
    let subst = create_subst penv.env.vars penv.isubst penv.msubst in
    Term.subst subst t
  in

  (* Used to get the 2nd and 3rd component associated to the string [v] in
   * the substitutions [isubst] or [msubst]. *)
  let list_assoc v l =
    let _,th,tm = List.find (fun (x,_,_) -> x = v) l in
    th,tm
  in

  let to_tsubst subst = List.map (fun (x,y,_) -> x,y) subst in

  (* Register an action, when we arrive at the end of a block
   * (input / condition / update / output). *)
  let register_action _loc a output (penv : p_env) =
    (* In strict alias mode, we require that the alias T is available. *)
    let exact = TConfig.strict_alias_mode (penv.env.table) in
    let table,a' = Action.fresh_symbol penv.env.table ~exact a in

    let action = List.rev penv.action in
    let in_ch, in_var = match penv.inputs with
    | (c,v) :: _ -> c, Vars.name v
    | _ -> assert false
    in
    let indices = List.rev penv.indices in
    let action_term = Term.mk_action a' (Term.mk_vars indices) in
    let in_th = Theory.var_i dum in_var in
    let in_tm = Term.mk_macro Term.in_macro [] action_term in

    (* substitute the special timestamp variable [ts], since at this point
     * we know the action *)
    let subst_ts = [ Term.ESubst (Term.mk_var ts, action_term) ] in

    (* override previous term substitution for input variable
    * to use the known action *)
    let subst_input =
      try [Term.ESubst (snd (list_assoc in_var penv.msubst), in_tm)]
      with Not_found -> []
    in

    let msubst' = try
        let x, _, _ = List.find (fun (_,x_th,_) ->
            match Theory.destr_var x_th with
            | Some x -> L.unloc x = in_var
            | None -> false)
            penv.msubst in
        (x,in_th,in_tm) :: penv.msubst
      (* in case of Not_found, it means it is a dummy input,
       * which cannot be used in the terms, so we don't need a substitution *)
      with Not_found -> penv.msubst
    in
    let penv = { penv with msubst = msubst' } in

    debug "register action %a@." Term.pp action_term ;
    debug "indices = %a@." Vars.pp_list penv.indices ;
    debug "input variables = %a@." Vars.pp_list (List.map snd penv.inputs) ;
    print_isubst penv.isubst ;
    print_msubst penv.msubst ;

    (* compute the condition, the updates, and the output of this action,
     * using elements we have stored in [env] of type [p_env] while parsing
     * the process *)
    let condition =
      List.rev penv.evars,
      Term.subst
        (subst_ts @ subst_input)
        (Term.mk_ands penv.facts) 
    in
    debug "condition = %a.@." Term.pp (snd condition);

    let updates =
      List.map (fun (s,args,_,t) ->
          let ms = Symbols.Macro.of_lsymb s penv.env.table in
          ms,
          args,
          Term.subst (subst_ts @ subst_input) t
        ) penv.updates
    in

    debug "updates = %a.@."
      (Utils.pp_list
         (fun ch (u,args,v) ->
            Format.fprintf ch "%a(%a) := %a" 
              Symbols.pp u
              Vars.pp_list args
              Term.pp v))
      updates ;

    let output = match output with
      | Some (c,t) ->
        let t = 
          (* FEATURE: subtypes *)
          Term.subst (subst_ts @ subst_input)
            (conv_term penv action_term t Type.Message) 
        in
        c, t
          
      | None -> Symbols.dummy_channel, Term.empty
    in

    debug "output = %a,%a.@."
      Channel.pp_channel (fst output) Term.pp (snd output) ;
    let action_descr = Action.{ 
        name    = a';
        action;
        input   = in_ch;
        indices = indices;
        globals = penv.globals; 
        condition; updates; output; } 
    in
    assert (Action.check_descr action_descr);

    let table, new_a, _ =
      System.register_action table system_name action_descr
    in

    let table =
      if new_a <> a' then Symbols.Action.release table a' else table
    in

    debug "descr = %a@." Action.pp_descr action_descr ;
    let new_action_term = 
      Term.mk_action new_a (Term.mk_vars action_descr.indices) 
    in
    let new_in_tm = Term.mk_macro Term.in_macro [] new_action_term in
    let penv =
      { penv with
        (* override previous term substitutions for input variable
         * to use possibly new action *)
        msubst = (in_var, in_th, new_in_tm) :: penv.msubst;

        (* pending globals have been registered with the previous action. *)
        globals = []; }
    in
    ({ penv with env = { penv.env with table } }, new_a)
  in

  (* common treatment of Apply, Alias and New constructs *)
  let p_common ~(penv : p_env) proc =
    match L.unloc proc with
    | Apply (id,args)
    | Alias (L.{ pl_desc = Apply (id,args) }, _) ->
      (* Keep explicit alias if there is one,
       * otherwise use id as the new alias. *)
      let a' = match L.unloc proc with Alias (_,a) -> a | _ -> id in
      let proc_ty, projs', p = find_process_lsymb penv.env.table id in

      if penv.projs <> projs' then
        error (L.loc proc) (ProjsMismatch (penv.projs, projs'));

      let new_env, isubst', msubst' =
        (* TODO avoid or handle conflicts with variables already
         * in domain of subst, i.e. variables bound above the apply *)
        let tsubst = (to_tsubst penv.isubst@to_tsubst penv.msubst) in
        List.fold_left2
          (fun (new_env,iacc,macc) (x, ty) v ->
             let new_env, _ = make_fresh `Shadow new_env ty x in

             match ty with
             | Type.Index ->
               let v'_th = Theory.subst v tsubst in
               let v'_tm : Term.term =
                 conv_term penv (Term.mk_var ts) v ty in
               let v'_tm = Utils.oget (Term.destr_var v'_tm) in

               new_env, (x, L.unloc v'_th, v'_tm) :: iacc, macc

             | Type.Timestamp -> assert false

             | _ ->
               let v'_th = Theory.subst v tsubst in
               let v'_tm : Term.term =
                 conv_term penv (Term.mk_var ts) v ty in

               new_env, iacc, (x, L.unloc v'_th, v'_tm) :: macc

          ) (penv, penv.isubst,penv.msubst) proc_ty args
      in

      let penv =
        { new_env with
          alias  = a' ;
          isubst = isubst' ;
          msubst = msubst' }
      in
      (penv,p)

  | New (n, pty, p) ->
    let ty = Theory.convert_ty penv.env pty in

    let n_fty = Type.mk_ftype_tuple [] (List.map Vars.ty penv.indices) ty in
    let ndef = Symbols.{ n_fty } in

    let table,n' = Symbols.Name.declare penv.env.table n ndef in
    let n'_th =
      let n' = L.mk_loc (L.loc n) (Symbols.to_string n') in
      Theory.mk_app_i
        (Theory.mk_symb n')
        (List.rev_map (fun i -> Theory.var dum (Vars.name i)) penv.indices)
    in    
    let n'_s = Term.mk_symb n' ty in
    let n'_tm = Term.mk_name n'_s (Term.mk_vars (List.rev penv.indices)) in

    let vars, _ = Vars.make_local `Shadow penv.env.vars ty (L.unloc n) in

    let penv = { penv with env = { penv.env with vars; table };
                           msubst = (L.unloc n,n'_th,n'_tm) :: penv.msubst }
    in
    (penv,p)

  | Alias (p,a) ->
    let penv = { penv with alias = a } in
    (penv,p)

  | _ -> assert false

  in

  (* treatment of Let(x,t,p) constructs
   * the boolean [in_update] indicates whether we are in the update phase:
   * In that case, we have to search in [t] if there are some get terms for 
   * state macros that have already been updated *)
  let p_let ?(in_update=false) ~(penv : p_env) proc = match L.unloc proc with

  | Let (x,t,ptyo,p) ->
    let ty : Type.ty = match ptyo with
      | None -> TUnivar (Type.Infer.mk_univar penv.ty_env)
      | Some pty -> Theory.convert_ty penv.env pty 
    in

    let t' = Theory.subst t (to_tsubst penv.isubst @ to_tsubst penv.msubst) in
    let updated_states =
      if in_update then
        let apps = List.map (fun (s,_,_,_) -> L.unloc s) penv.updates in
        Theory.find_app_terms t' apps 
      else []
    in

    let body : Term.term =
      Term.subst_macros_ts penv.env.table updated_states (Term.mk_var ts)
        (conv_term penv (Term.mk_var ts) t ty)
    in

    (* We check that we could infer ty by parsing [t] *)
    let ty = match Type.Infer.norm penv.ty_env ty with
      | Type.TUnivar _ -> error (L.loc proc) Freetyunivar
      | _ as ty -> ty
    in

    let invars = List.map snd penv.inputs in
    let shape = Action.get_shape_v (List.rev penv.action) in
    let table, x' =
      let suffix = if in_update then `Large else `Strict in
      Macros.declare_global penv.env.table system_name x
        ~suffix
        ~action:shape ~inputs:invars
        ~indices:(List.rev penv.indices) ~ts body ty
    in

    let x'_th =
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in
      let is =
        List.rev_map (fun i -> Theory.var dum (Vars.name i)) penv.indices
      in
      Theory.mk_app_i (Theory.mk_symb x') is
    in

    let n'_s = Term.mk_symb x' ty in
    let args = Term.mk_vars (List.rev penv.indices) in
    let x'_tm = Term.mk_macro n'_s args (Term.mk_var ts) in

    let vars, _ = Vars.make_local `Shadow penv.env.vars ty (L.unloc x) in
    
    let penv =
      { penv with env = { penv.env with vars; table}; 
                  msubst = (L.unloc x,x'_th,x'_tm) :: penv.msubst;
                  globals = x' :: penv.globals; }
    in
    (x', t', penv, p)

  | _ -> assert false

  in

  (* Parse process, looking for an input action.
     Maintains the position [pos] in parallel compositions,
     together with the indices [pos_indices] associated to replications:
     these two components will form the [par_choice] part of an
     [Action.item]. *)
  let rec p_in ~penv ?(table=penv.env.table) ~pos ~pos_indices proc =
    let penv = { penv with env = { penv.env with table } } in

    let p, pos, table = p_in_i ~penv ~pos ~pos_indices proc in
    (L.mk_loc (L.loc proc) p, pos, table)

  and p_in_i ~penv ~pos ~pos_indices proc =
    match L.unloc proc with
    | Null -> (Null,pos,penv.env.table)

    | Parallel (p,q) ->
      let p',pos_p,table = p_in ~penv ~pos ~pos_indices p in
      let q',pos_q,table = p_in ~table ~penv ~pos:pos_p ~pos_indices q in
      ( Parallel (p',q'),
        pos_q,
        table)

    | Repl (i,p) ->
      let penv,i' = make_fresh `Shadow penv Type.Index (L.unloc i) in
      let penv =
        { penv with
          isubst = (L.unloc i, Theory.var_i dum (Vars.name i'), i') :: penv.isubst ;
          indices = i' :: penv.indices }
      in
      let pos_indices = i'::pos_indices in
      let p',pos',table = p_in ~penv ~pos ~pos_indices p in
      ( Repl (L.mk_loc (L.loc i) (Vars.name i'), p'),
        pos',
        table )

    | Apply _ | Alias _ | New _ ->
      let penv,p = p_common ~penv proc in
      p_in_i ~penv ~pos ~pos_indices p

    | Let (x,_,ty,_) ->
      let x',t',penv,p = p_let ~penv proc in
      let p',pos',table = p_in ~penv ~pos ~pos_indices p in
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in

      ( Let (x', t',ty,p'),
        pos',
        table)

    | In (c,x,p) ->
      let ch = Channel.of_lsymb c penv.env.table in
      (* FEATURE: subtypes *)
      let penv,x' = make_fresh `Shadow penv Type.Message (L.unloc x) in
      let in_th = Theory.var_i dum (Vars.name x') in
      let in_tm = Term.mk_var x' in
      let penv = { penv with
                   inputs = (ch,x')::penv.inputs ;
                   msubst = (L.unloc x, in_th, in_tm) :: penv.msubst }
      in

      let par_choice = pos, List.rev pos_indices in
      let (p',_,table : process * int * Symbols.table) =
        p_cond ~penv ~pos:0 ~par_choice p in
      let x' = L.mk_loc (L.loc x) (Vars.name x') in

      ( In (c,x',p'),
        pos+1,
        table )

    | Exists _ | Set _ | Out _ ->
      let penv =
        { penv with
          inputs = (Symbols.dummy_channel,dummy_in)::penv.inputs } in
      let par_choice = pos, List.rev pos_indices in
      let p',_,table = p_cond_i ~penv ~pos:0 ~par_choice proc in
      (p', pos+1,table)

  (* Similar to [p_in].
     The [par_choice] component of the action under construction
     has been determined by [p_in].
     The [pos] argument is the position in the tree of conditionals. *)
  and p_cond ~penv ?(table=penv.env.table) ~pos ~par_choice proc =
    let penv = { penv with env = { penv.env with table } } in

    let p, pos, table = p_cond_i ~penv ~pos ~par_choice proc in
    (L.mk_loc (L.loc proc) p, pos, table)

  and p_cond_i ~penv ~pos ~par_choice proc =
    match L.unloc proc with
    | Apply _ | Alias _ | New _ ->
      let penv,p = p_common ~penv proc in
      p_cond_i ~penv ~pos ~par_choice p

    | Let (x,_,ty,_) ->
      let x',t',penv,p = p_let ~penv proc in
      let p',pos',table = p_cond ~penv ~pos ~par_choice p in
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in

      ( Let (x', t',ty,p'),
        pos',
        table )

    | Exists (evars, cond, p, q) ->
      let penv_p,s =
        List.fold_left (fun (penv,s) i ->
            let i = L.unloc i in
             let penv,i' = make_fresh `Shadow penv Type.Index i in
            penv,(i,i') :: s
          ) (penv,[]) (List.rev evars)
      in
      let evars' = List.map snd s in
      let isubst' =
        List.map
          (fun (i,i') -> i, Theory.var_i dum (Vars.name i'), i')
          s
        @ penv_p.isubst
      in
      let penv_p = { penv_p with isubst = isubst' } in
      let cond' =
        Theory.subst cond (to_tsubst penv_p.isubst @ to_tsubst penv_p.msubst)
      in

      (* No state updates have been done yet in the current
       * action. We thus have to substitute [ts] by [pred(ts)] for all state
       * macros appearing in [t]. This is why we call [Term.subst_macros_ts]
       * with the empty list. *)
      let fact =
        Term.subst_macros_ts penv.env.table [] (Term.mk_var ts)
          (conv_term penv_p (Term.mk_var ts) cond Type.Boolean)
      in
      let facts_p = fact :: penv.facts in
      let facts_q =
        match evars' with
        | [] -> (Term.mk_not fact) :: penv.facts
        | qvars -> 
          Term.mk_forall ~simpl:false qvars (Term.mk_not fact) :: penv.facts
      in
      let penv_p =
        { penv_p with
          indices = List.rev_append (List.map snd s) penv.indices ;
          isubst = isubst' ;
          evars = List.rev_append (List.map snd s) penv.evars ;
          facts = facts_p }
      in
      let penv_q = { penv with facts = facts_q } in
      let p',pos_p,table = p_cond ~penv:penv_p ~pos ~par_choice p in
      let q',pos_q,table = p_cond ~table ~penv:penv_q ~pos:pos_p ~par_choice q in

      (* [evs] could re-use the locations of [evars] *)
      let evs = List.map (fun (_,x) -> mk_dum (Vars.name x)) s in

      ( Exists (evs,cond',p',q'),
        pos_q,
        table )

    | _ ->
      (* We are done processing conditionals, let's prepare
       * for the next step, i.e. updates and output.
       * At this point we know which action will be used,
       * but we don't have the action symbol yet. *)
      let vars = List.rev penv.evars in
      let penv =
        { penv with
          action = Action.{ 
              par_choice ;
              sum_choice = pos, vars } :: penv.action }
      in
      let p',_,table = p_update_i ~penv proc in
      (p', pos + 1,table)


  and p_update ~penv (proc : process) =
    let p, pos, table = p_update_i ~penv proc in
    (L.mk_loc (L.loc proc) p, pos, table)

  and p_update_i ~penv (proc : process) =
    let loc = L.loc proc in
    match L.unloc proc with
    | Apply _ | Alias _ | New _ ->
      let penv,p = p_common ~penv proc in
      p_update_i ~penv p

    | Let (x,_,ty,_) ->
      let x',t',penv,p = p_let ~in_update:true ~penv proc in
      let p',pos',table = p_update ~penv p in
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in

      ( Let (x', t',ty,p'),
        pos',
        table )

    | Set (s,l,t,p) ->
      if List.exists (fun (s',_,_,_) -> L.unloc s = L.unloc s') penv.updates
      then
        (* Not allowed because a state macro can have only 2 values:
           - either the value at the end of the current action,
           - either the value before the current action.
             There is no in-between value. *)
        error loc (DuplicatedUpdate (L.unloc s));

      let t' = Theory.subst t (to_tsubst penv.isubst @ to_tsubst penv.msubst) in
      let l' =
        List.map
          (fun i ->
             snd (list_assoc (L.unloc i) penv.isubst))
          l
      in
      let updated_states =
        let apps = List.map (fun (s,_,_,_) -> L.unloc s) penv.updates in
        Theory.find_app_terms t' apps            
      in
      let ty = Theory.check_state penv.env.table s (List.length l) in
      let t'_tm =
        Term.subst_macros_ts penv.env.table updated_states (Term.mk_var ts)
          (conv_term penv (Term.mk_var ts) t ty)
      in
      let penv =
        { penv with updates = (s,l',ty,t'_tm) :: penv.updates }
      in
      let p',pos',table = p_update ~penv p in

      (* we could re-use the location in [l] here. *)
      let l' = List.map (fun x -> mk_dum (Vars.name x)) l' in

      ( Set (s,l',t',p'),
        pos',
        table )

    | Out (c,t,p) ->
      let ch = Channel.of_lsymb c penv.env.table in
      let t' = Theory.subst t (to_tsubst penv.isubst @ to_tsubst penv.msubst) in

      let penv,a' = register_action loc penv.alias (Some (ch,t)) penv in
      let penv =
        { penv with
          evars = [] ;
          facts = [] ;
          updates = [] }
      in
      let p',pos',table = p_in ~penv ~pos:0 ~pos_indices:[] p in
      (* The same location re-used twice, as both sub-processes come from the
         same initial process. *)
      let p' = L.mk_loc loc (Out (c,t',p')) in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (p', a'),
        pos',
        table )

    | Null ->
      let penv,a' = register_action loc penv.alias None penv in
      let pnull = L.mk_loc loc Null in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (pnull, a'),
        0,
        penv.env.table)

    | In _ | Parallel _ | Repl _ | Exists _ ->
      let penv,a' = register_action loc penv.alias None penv in
      let penv =
        { penv with
          evars = [] ;
          facts = [] ;
          updates = [] }
      in
      let p',pos',table = p_in ~penv ~pos:0 ~pos_indices:[] proc in

      let c_dummy = Symbols.dummy_channel_lsymb in

      let p'_i = Out (c_dummy, Theory.empty dum,p') in
      let p' = L.mk_loc loc p'_i in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (p', a'),
        pos',
        table )

  in

  let env = Env.init ~table:init_table ~vars:env_ts () in
  let penv =
    { ty_env   = Type.Infer.mk_env ();
      projs    = init_projs;
      alias    = L.mk_loc L._dummy "A" ;
      indices  = [] ;
      env;
      isubst   = [] ;
      msubst   = [] ;
      inputs   = [] ;
      evars    = [] ;
      action   = [] ;
      facts    = [] ;
      updates  = [];
      globals  = []; }
  in

  let proc,_,table = p_in ~table:init_table ~penv ~pos:0 ~pos_indices:[] proc in

  (* I believe this test is not useful *)
  if not (Type.Infer.is_closed penv.ty_env) then 
    error (L.loc proc) Freetyunivar;

  (proc, table)

(*------------------------------------------------------------------*)
(** {2 System declaration } *)

let declare_system table system_name (projs : Term.projs) (proc : process) =
  Printer.pr
    "@[<v 2>System before processing:@;@;@[%a@]@]@.@."
    pp_process proc ;

  let env = Env.init ~table () in
  check_proc env projs proc ;

  (* FEATURE: allow user to define more than bi-system *)
  let projections = [Term.left_proj; Term.right_proj] in
  let system_name = match system_name with
    | Some lsymb -> lsymb
    | None -> L.mk_loc Location._dummy "default"
  in
  let table,system_name = System.declare_empty table system_name projections in

  (* we register the init action before parsing the system *)
  let init_descr = Action.{ 
      name      = Symbols.init_action;
      action    = [];
      input     = Symbols.dummy_channel;
      indices   = [];
      condition = ([], Term.mk_true);
      updates   = Theory.get_init_states table;
      output    = (Symbols.dummy_channel, Term.empty);
      globals   = []; }
  in
  let table, _, _ =
    System.register_action table system_name init_descr
  in

  (* parse the processus *)
  let proc,table = parse_proc system_name table projs proc in

  let table = Lemma.add_depends_mutex_lemmas table system_name in
  
  Printer.pr "@[<v 2>System after processing:@;@;@[%a@]@]@.@." pp_process proc ;
  Printer.pr "%a" System.pp_systems table;
  table
