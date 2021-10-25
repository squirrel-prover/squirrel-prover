module L = Location

let dum : L.t = L._dummy

(** We use dummy locations for intermediary term we build, which do not come
    from the user. *)
let mk_dum (v : 'a) : 'a L.located = L.mk_loc dum v

(*------------------------------------------------------------------*)
type proc_ty = (string * Type.ety) list

let pp_proc_ty =
  let pp_el fmt (s,e) = Fmt.pf fmt "(%s : %a)" s Type.pp_e e in
  (Fmt.list pp_el)

(*------------------------------------------------------------------*)
type id = string
type lsymb = Theory.lsymb

type term = Theory.term
type formula = Theory.formula

(*------------------------------------------------------------------*)
type process_i =
  | Null
  | New of lsymb * Theory.p_ty * process
  | In  of Channel.p_channel * lsymb * process
  | Out of Channel.p_channel * term * process
  | Parallel of process * process
  | Set of lsymb * lsymb list * term * process
  | Let of lsymb * term * Theory.p_ty option * process
  | Repl of lsymb * process
  | Exists of lsymb list * formula * process * process
  | Apply of lsymb * term list
  | Alias of process * lsymb

and process = process_i L.located

(*------------------------------------------------------------------*)
let rec pp_process ppf process =
  let open Fmt in
  let open Utils in
  match L.unloc process with
  | Null ->  (styled `Blue (styled `Bold ident)) ppf "null"

  | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (styled `Bold (styled `Blue ident)) (L.unloc s)
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
      (kw `Bold) ":="
      Theory.pp t
      pp_process p

  | New (s, t, p) when L.unloc t = Theory.P_message ->
    pf ppf "@[<hov>%a %a;@ @[%a@]@]"
      (kw `Red) "new"
      (kw `Magenta) (L.unloc s)
      pp_process p

  | New (s, t, p) ->
    pf ppf "@[<hov>%a %a : %a;@ @[%a@]@]"
      (kw `Red) "new"
      (kw `Magenta) (L.unloc s)
      Theory.pp_p_ty t
      pp_process p

  | In (c, s, p) ->
    pf ppf "@[<hov>%a(%s,@,%a);@ %a@]"
      (kw `Bold) "in"
      (L.unloc c)
      (styled `Magenta (styled `Bold ident)) (L.unloc s)
      pp_process p

  | Out (c, t, p) ->
    pf ppf "@[<hov>%a(%s,@,%a);@ %a@]"
      (kw `Bold) "out"
      (L.unloc c)
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
      (kw `Bold) "let"
      (styled `Magenta (styled `Bold ident)) (L.unloc s)
      pp_tyo tyo
      Theory.pp t
      (styled `Bold ident) "in"
      pp_process p

  | Exists (ss, f, p1, p2) ->
    if ss = [] then
      pf ppf "@[<hov>%a %a %a@;<1 2>%a"
        (styled `Red (styled `Underline ident)) "if"
        Theory.pp f
        (styled `Red (styled `Underline ident)) "then"
        pp_process p1
    else
      pf ppf "@[<hov>%a %a %a %a %a@;<1 2>%a"
        (styled `Red (styled `Underline ident)) "find"
        (Utils.pp_list Fmt.string) (L.unlocs ss)
        (styled `Red (styled `Underline ident)) "such that"
        Theory.pp f
        (styled `Red (styled `Underline ident)) "in"
        pp_process p1 ;
    if L.unloc p2 <> Null then
      pf ppf "@ %a@;<1 2>%a@]"
      (styled `Red (styled `Underline ident)) "else"
      pp_process p2
    else
      pf ppf "@]"

(*------------------------------------------------------------------*)
let is_out_i = function Out _ -> true | _ -> false
let is_out p = is_out_i (L.unloc p)

(*------------------------------------------------------------------*)
type proc_error_i =
  | Arity_error of string * int * int
  | StrictAliasError of string
  | DuplicatedUpdate of string
  | Freetyunivar

type proc_error = L.t * proc_error_i

let pp_proc_error_i fmt = function
  | StrictAliasError s -> Fmt.pf fmt "strict alias error: %s" s

  | Arity_error (s,i,j) -> 
    Fmt.pf fmt "process %s used with arity %i, but \
                defined with arity %i" s i j

  | DuplicatedUpdate s -> 
    Fmt.pf fmt "state %s can only be updated once in an action" s

  | Freetyunivar -> Fmt.pf fmt "some type variable(s) could not \
                                be instantiated"

let pp_proc_error pp_loc_err fmt (loc,e) =
  Fmt.pf fmt "%aproc error: %a."
    pp_loc_err loc
    pp_proc_error_i e

exception ProcError of proc_error

let proc_err loc e = raise (ProcError (loc,e))

(*------------------------------------------------------------------*)
(** We extend the symbols data with (bi)-processus descriptions and
    their types. *)
type Symbols.data += Process_data of proc_ty * process

let declare_nocheck table name (kind : proc_ty) proc =
    let data = Process_data (kind,proc) in
    let def = () in
    Symbols.Process.declare_exact table name ~data def

let find_process table pname =
  match Symbols.Process.get_all pname table with
  | (), Process_data (kind,proc) -> kind,proc
  | _ -> assert false
  (* The data associated to a process must be a [Process_data _]. *)

let find_process_lsymb table (lsymb : lsymb) =
  let name = Symbols.Process.of_lsymb lsymb table in
  find_process table name

let check_channel table (s : lsymb) =
  ignore(Channel.of_lsymb s table : Channel.t)

(*------------------------------------------------------------------*)
(** Type checking for processes *)
let check_proc table (env : Vars.env) p =
  let rec check_p ty_env (env : Vars.env) proc =
    let loc = L.loc proc in
    match L.unloc proc with
    | Null -> ()

    | New (x, ty, p) -> 
      let ty = Theory.parse_p_ty table [] ty Type.KMessage in 
      let env, _ = Vars.make `Shadow env ty (L.unloc x) in
      check_p ty_env env p

    | In (c,x,p) -> 
      check_channel table c;

      (* TODO: subtypes*)
      let env, _ = Vars.make `Shadow env (Type.Message) (L.unloc x) in
      check_p ty_env env p

    | Out (c,m,p)

    | Alias (L.{ pl_desc = Out (c,m,p) },_) ->
      check_channel table c;

      (* raise an error if we are in strict alias mode *)
      if is_out proc && (Config.strict_alias_mode ())
      then proc_err loc (StrictAliasError "missing alias")
      else
        (* TODO: subtypes *)
        let () = Theory.check table ~local:true ty_env env m Type.emessage in
        check_p ty_env  env p

    | Alias (p,_) -> check_p ty_env  env p

    | Set (s, l, m, p) ->
      let k = Theory.check_state table s (List.length l) in
      Theory.check table ~local:true ty_env env m (Type.ETy k) ;
      List.iter (fun x ->
          Theory.check
            table ~local:true ty_env env
            (Theory.var_of_lsymb x) Type.eindex
        ) l ;
      check_p ty_env  env p

    | Parallel (p, q) -> check_p ty_env  env p ; check_p ty_env  env q

    | Let (x, t, ptyo, p) ->
      let ty : Type.tmessage = match ptyo with
        | None -> TUnivar (Type.Infer.mk_univar ty_env)
        | Some pty -> Theory.parse_p_ty table [] pty Type.KMessage
      in
      
      let ety = Type.ETy ty in
      Theory.check table ~local:true ty_env env t ety ;
      let env, _ = Vars.make `Shadow env ty (L.unloc x) in
      check_p ty_env env p

    | Repl (x, p) -> 
      let env, _ = Vars.make `Shadow env Type.Index (L.unloc x) in
      check_p ty_env env p

    | Exists (vars, test, p, q) ->
      check_p ty_env  env q ;
      let env =
        List.fold_left (fun env x ->
            let env, _ = Vars.make `Shadow env Type.Index (L.unloc x) in
            env
          ) env vars 
      in
      Theory.check table ~local:true ty_env env test Type.eboolean ;
      check_p ty_env  env p

    | Apply (id, ts) ->
      let kind,_ = find_process_lsymb table id in
      if List.length kind <> List.length ts then
        proc_err loc (Arity_error (L.unloc id,
                                   List.length ts,
                                   List.length kind));
      List.iter2
        (fun (_, k) t -> Theory.check table ~local:true ty_env env t k)
        kind ts
  in

  let ty_env = Type.Infer.mk_env () in

  check_p ty_env env p;

  if not (Type.Infer.is_closed ty_env) then
    proc_err (L.loc p) Freetyunivar;

  ()


let declare table (id : lsymb) (args : proc_ty) proc =
  let env = 
    List.fold_left (fun env (v, Type.ETy ty) ->
        let env, _ = Vars.make `Shadow env ty v in
        env
      ) Vars.empty_env args 
  in

  (* type-check and declare *)
  check_proc table env proc ;
  let table, _ = declare_nocheck table id args proc in
  table

(*------------------------------------------------------------------*)
(* Enable/disable debug messages by setting debug to debug_on/off. *)

let debug_off fmt = Format.fprintf Printer.dummy_fmt fmt
let debug_on fmt =
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

  alias : lsymb ;
  (* current alias used for action names in the process *)

  indices : Vars.index list ;
  (* current list of bound indices (coming from Repl or Exists constructs) *)

  vars_env : Vars.env ;
  (* local variables environment *)

  isubst : (string * Theory.term_i * Vars.index) list ;
  (* substitution for index variables (Repl, Exists, Apply)
   * mapping each variable from the original process (before refresh)
   * to the associated refreshed variables
   * as Theory.term and as a Vars.index suitable for use in Term.term
   * TODO items are always of the form (i, Theory.Var (Vars.name i'), i')
   *      why not keep (i,i') for simplicity? *)

  msubst : (string * Theory.term_i * Term.message) list ;
  (* substitution for message variables (New, Let, In, Apply)
   * each variable from the original process (before refresh)
   * is mapped to the associated refreshed variable
   * as a Theory.term and as a Term.message
   * (the third component is also used to map input variables to
   * input macros) *)

  inputs : (Channel.t * Vars.message) list ;
  (* bound input variables *)

  (* RELATED TO THE CURRENT ACTION *)
  evars : Vars.index list ;
  (* variables bound by existential quantification *)

  action : Action.action ;
  (* the type [Action.action] describes the execution point in the protocol
     stored reversed *)

  facts : Term.message list ;
  (* list of formulas to create the condition term of the action *)

  updates : (lsymb * Vars.index list * Type.tmessage * Term.message) list ;
  (* list of updates performed in the action.
   * The type can be a type unification variables. *)

  globals : Symbols.macro Symbols.t list;
  (* list of global macros declared at [action] *)

}

let parse_proc (system_name : System.system_name) init_table proc =

  (* Initial env with special variables registered.
   * The special variables should never be visible to the user,
   * we prefix their names with $ to avoid conflicts with user names,
   * and also register special variables in the environment for extra
   * safety. *)
  let env_ts,ts,dummy_in =
    let env = Vars.empty_env in
    let env,ts = Vars.make `Shadow env Type.Timestamp "$ts" in
    let env,dummy_in = Vars.make `Shadow env Type.Message "$dummy" in
    env,ts,dummy_in
  in

  (* Update env.vars_env with a new variable of sort [sort] computed from
   * [name] *)
  let make_fresh param env sort name =
    let ve',x = Vars.make param env.vars_env sort name in
    { env with vars_env = ve' }, x
  in

  let create_subst env isubst msubst =
    List.map (fun (x,_,tm) -> 
        let v = Vars.find env x Type.KIndex in
        Term.ESubst (Term.mk_var v, Term.mk_var tm)
      ) isubst
    @
    List.map (fun (x,_,tm) -> 
        let v = Vars.find env x Type.KMessage in
        Term.ESubst (Term.mk_var v, tm)
      ) msubst
  in

  (* Convert a Theory.term to Term.term using the special sort
   * of substitution ([isubst] and [msubst]) maintained by the
   * parsing function.
   * The special timestamp variable [ts] is used. *)
  let conv_term : type a.
    Symbols.table -> p_env -> Term.timestamp -> 
    Theory.term -> a Type.ty -> a Term.term =
    fun table env ts t sort ->
    let t = 
      Theory.convert ~ty_env:env.ty_env
        { table = table; cntxt = InProc ts; } [] env.vars_env t sort
    in
    let subst = create_subst env.vars_env env.isubst env.msubst in
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
  let register_action loc a output table env =
    (* In strict alias mode, we require that the alias T is available. *)
    let exact = Config.strict_alias_mode () in
    let table,a' = Action.fresh_symbol table ~exact a in

    let action = List.rev env.action in
    let in_ch, in_var = match env.inputs with
    | (c,v)::_ -> (c,Vars.name v)
    | _ -> assert false
    in
    let indices = List.rev env.indices in
    let action_term = Term.mk_action a' indices in
    let in_th = Theory.var_i dum in_var in
    let in_tm = Term.mk_macro Term.in_macro [] action_term in

    (* substitute the special timestamp variable [ts], since at this point
     * we know the action *)
    let subst_ts = [ Term.ESubst (Term.mk_var ts, action_term) ] in

    (* override previous term substitution for input variable
    * to use the known action *)
    let subst_input =
      try [Term.ESubst (snd (list_assoc (in_var) env.msubst), in_tm)]
      with Not_found -> []
    in

    let msubst' = try
        let x, _, _ = List.find (fun (_,x_th,_) ->
            match Theory.destr_var x_th with
            | Some x -> L.unloc x = in_var
            | None -> false)
            env.msubst in
        (x,in_th,in_tm) :: env.msubst
      (* in case of Not_found, it means it is a dummy input,
       * which cannot be used in the terms, so we don't need a substitution *)
      with Not_found -> env.msubst
    in
    let env = { env with msubst = msubst' } in

    debug "register action %a@." Term.pp action_term ;
    debug "indices = %a@." Vars.pp_list env.indices ;
    debug "input variables = %a@." Vars.pp_list (List.map snd env.inputs) ;
    print_isubst env.isubst ;
    print_msubst env.msubst ;

    (* compute the condition, the updates, and the output of this action,
     * using elements we have stored in [env] of type [p_env] while parsing
     * the process *)
    let condition =
      List.rev env.evars,
      Term.subst
        (subst_ts @ subst_input)
        (Term.mk_ands env.facts)
    in

    let updates =
      List.map (fun (s,l,ty,t) ->
          let ms = Symbols.Macro.of_lsymb s table in
          Term.mk_isymb ms ty l,
           Term.subst (subst_ts @ subst_input) t
        ) env.updates
    in

    debug "updates = %a.@."
      (Utils.pp_list
         (fun ch (u,v) ->
            Format.fprintf ch "_ := %a" Term.pp v))
      updates ;

    let output = match output with
      | Some (c,t) ->
        let t = 
          (* TODO: subtypes *)
          Term.subst (subst_ts @ subst_input)
            (conv_term table env action_term t Type.Message) 
        in
        c, t
          
      | None -> Symbols.dummy_channel, Term.empty
    in

    debug "output = %a,%a.@."
      Channel.pp_channel (fst output) Term.pp (snd output) ;
    let action_descr = Action.{ 
        name    = a';
        action;
        input   = (in_ch, in_var);
        indices = indices;
        globals = env.globals; 
        condition; updates; output; } 
    in

    let table, new_a, action_descr =
      System.register_action table system_name a' indices action action_descr
    in

    debug "descr = %a@." Action.pp_descr action_descr ;
    let new_indices = action_descr.indices in
    let new_action_term = Term.mk_action new_a new_indices in
    let new_in_tm = Term.mk_macro Term.in_macro [] new_action_term in
    let env =
      { env with
        (* override previous term substitutions for input variable
         * to use possibly new action *)
        msubst = (in_var, in_th, new_in_tm) :: env.msubst;

        (* pending globals have been registered with the previous action. *)
        globals = []; }
    in
    (table, env, new_a)
  in

  (* common treatment of Apply, Alias and New constructs *)
  let p_common ~table ~env proc =
    match L.unloc proc with
    | Apply (id,args)
    | Alias (L.{ pl_desc = Apply (id,args) }, _) ->
      (* Keep explicit alias if there is one,
       * otherwise use id as the new alias. *)
      let a' = match L.unloc proc with Alias (_,a) -> a | _ -> id in
      let proc_ty, p = find_process_lsymb table id in

      let new_env, isubst', msubst' =
        (* TODO avoid or handle conflicts with variables already
         * in domain of subst, i.e. variables bound above the apply *)
        let tsubst = (to_tsubst env.isubst@to_tsubst env.msubst) in
        List.fold_left2
          (fun (new_env,iacc,macc) (x,Type.ETy ty) v ->
             let new_env, _ = make_fresh `Shadow new_env ty x in

             match Type.kind ty with
             | Type.KMessage ->
               let v'_th = Theory.subst v tsubst in
               let v'_tm : Term.message =
                 conv_term table env (Term.mk_var ts) v ty in

               new_env, iacc, (x, L.unloc v'_th, v'_tm) :: macc

             | Type.KIndex ->
               let v'_th = Theory.subst v tsubst in
               let v'_tm : Type.index Term.term =
                 conv_term table env (Term.mk_var ts) v ty in
               let v'_tm = Utils.oget (Term.destr_var v'_tm) in

               new_env, (x, L.unloc v'_th, v'_tm) :: iacc, macc
               
             | _ -> assert false
          ) (env, env.isubst,env.msubst) proc_ty args
      in

      let env =
        { new_env with
          alias  = a' ;
          isubst = isubst' ;
          msubst = msubst' }
      in
      (table,env,p)

  | New (n, pty, p) ->
    let ty = Theory.parse_p_ty table [] pty Type.KMessage in

    (* TODO getting a globally fresh symbol for the name
     * does not prevent conflicts with variables bound in
     * the process (in Repl, Let, In...) *)
    let ndef = Symbols.{ n_iarr = List.length env.indices; 
                         n_ty   = ty; } in

    let table,n' = Symbols.Name.declare table n ndef in
    let n'_th =
      let n' = L.mk_loc (L.loc n) (Symbols.to_string n') in
      Theory.App
        ( n',
          List.rev_map (fun i -> Theory.var dum (Vars.name i)) env.indices )
    in    
    let n'_s = Term.mk_isymb n' ty (List.rev env.indices) in
    let n'_tm = Term.mk_name n'_s in

    let vars_env, _ = Vars.make `Shadow env.vars_env ty (L.unloc n) in

    let env = { env with vars_env;
                         msubst = (L.unloc n,n'_th,n'_tm) :: env.msubst }
    in
    (table,env,p)

  | Alias (p,a) ->
    let env = { env with alias = a } in
    (table,env,p)

  | _ -> assert false

  in

  (* treatment of Let(x,t,p) constructs
   * the boolean [in_update] indicates whether we are in the update phase:
   * In that case, we have to search in [t] if there are some get terms for 
   * state macros that have already been updated *)
  let p_let ?(in_update=false) ~table ~env proc = match L.unloc proc with

  | Let (x,t,ptyo,p) ->
    let ty : Type.tmessage = match ptyo with
      | None -> TUnivar (Type.Infer.mk_univar env.ty_env)
      | Some pty -> Theory.parse_p_ty table [] pty Type.KMessage
    in

    let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
    let updated_states =
      if in_update then
        let apps = List.map (fun (s,_,_,_) -> L.unloc s) env.updates in
        Theory.find_app_terms t' apps 
      else []
    in

    let body : Term.message =
      Term.subst_macros_ts table updated_states (Term.mk_var ts)
        (conv_term table env (Term.mk_var ts) t ty)
    in

    (* We check that we could infer ty by parsing [t] *)
    let ty = match Type.Infer.norm env.ty_env ty with
      | Type.TUnivar _ -> proc_err (L.loc proc) Freetyunivar
      | _ as ty -> ty
    in

    let invars = List.map snd env.inputs in
    let shape = Action.get_shape (List.rev env.action) in
    let table,x' =
      let suffix = if in_update then `Large else `Strict in
      Macros.declare_global table x
        ~suffix
        ~action:shape ~inputs:invars
        ~indices:(List.rev env.indices) ~ts body ty
    in

    let x'_th =
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in
      let is =
        List.rev_map (fun i -> Theory.var dum (Vars.name i)) env.indices
      in
      Theory.App (x', is)
    in

    let n'_s = Term.mk_isymb x' ty (List.rev env.indices) in
    let x'_tm = Term.mk_macro n'_s [] (Term.mk_var ts) in

    let vars_env, _ = Vars.make `Shadow env.vars_env ty (L.unloc x) in
    
    let env =
      { env with vars_env; 
                 msubst = (L.unloc x,x'_th,x'_tm) :: env.msubst;
                 globals = x' :: env.globals; }
    in
    (x',t',table,env,p)

  | _ -> assert false

  in

  (** Parse process, looking for an input action.
    * Maintains the position [pos] in parallel compositions,
    * together with the indices [pos_indices] associated to replications:
    * these two components will form the [par_choice] part of an
    * [Action.item]. *)
  let rec p_in ~table ~env ~pos ~pos_indices proc =
    let p, pos, table = p_in_i ~table ~env ~pos ~pos_indices proc in
    (L.mk_loc (L.loc proc) p, pos, table)

  and p_in_i ~table ~env ~pos ~pos_indices proc =
    match L.unloc proc with
    | Null -> (Null,pos,table)

    | Parallel (p,q) ->
      let p',pos_p,table = p_in ~table ~env ~pos ~pos_indices p in
      let q',pos_q,table = p_in ~table ~env ~pos:pos_p ~pos_indices q in
      ( Parallel (p',q'),
        pos_q,
        table)

    | Repl (i,p) ->
      let env,i' = make_fresh `Shadow env Type.Index (L.unloc i) in
      let env =
        { env with
          isubst = (L.unloc i, Theory.var_i dum (Vars.name i'), i') :: env.isubst ;
          indices = i' :: env.indices }
      in
      let pos_indices = i'::pos_indices in
      let p',pos',table = p_in ~table ~env ~pos ~pos_indices p in
      ( Repl (L.mk_loc (L.loc i) (Vars.name i'), p'),
        pos',
        table )

    | Apply _ | Alias _ | New _ ->
      let table,env,p = p_common ~table ~env proc in
      p_in_i ~table ~env ~pos ~pos_indices p

    | Let (x,t,ty,p) ->
      let x',t',table,env,p = p_let ~table ~env proc in
      let p',pos',table = p_in ~table ~env ~pos ~pos_indices p in
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in

      ( Let (x', t',ty,p'),
        pos',
        table)

    | In (c,x,p) ->
      let ch = Channel.of_lsymb c table in
      (* TODO: subtypes*)
      let env,x' = make_fresh `Shadow env Type.Message (L.unloc x) in
      let in_th = Theory.var_i dum (Vars.name x') in
      let in_tm = Term.mk_var x' in
      let env = { env with
                  inputs = (ch,x')::env.inputs ;
                  msubst = (L.unloc x, in_th, in_tm) :: env.msubst }
      in

      let par_choice = pos, List.rev pos_indices in
      let (p',_,table : process * int * Symbols.table) =
        p_cond ~table ~env ~pos:0 ~par_choice p in
      let x' = L.mk_loc (L.loc x) (Vars.name x') in

      ( In (c,x',p'),
        pos+1,
        table )

    | Exists _ | Set _ | Out _ ->
      let env =
        { env with
          inputs = (Symbols.dummy_channel,dummy_in)::env.inputs } in
      let par_choice = pos, List.rev pos_indices in
      let p',_,table = p_cond_i ~table ~env ~pos:0 ~par_choice proc in
      (p', pos+1,table)

  (** Similar to [p_in].
    * The [par_choice] component of the action under construction
    * has been determined by [p_in].
    * The [pos] argument is the position in the tree of conditionals. *)
  and p_cond ~table ~env ~pos ~par_choice proc =
    let p, pos, table = p_cond_i ~table ~env ~pos ~par_choice proc in
    (L.mk_loc (L.loc proc) p, pos, table)

  and p_cond_i ~table ~env ~pos ~par_choice proc =
    match L.unloc proc with
    | Apply _ | Alias _ | New _ ->
      let table,env,p = p_common ~table ~env proc in
      p_cond_i ~table ~env ~pos ~par_choice p

    | Let (x,t,ty,p) ->
      let x',t',table,env,p = p_let ~table ~env proc in
      let p',pos',table = p_cond ~table ~env ~pos ~par_choice p in
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in

      ( Let (x', t',ty,p'),
        pos',
        table )

    | Exists (evars, cond, p, q) ->
      let env_p,s =
        List.fold_left (fun (env,s) i ->
            let i = L.unloc i in
             let env,i' = make_fresh `Shadow env Type.Index i in
            env,(i,i') :: s
          ) (env,[]) (List.rev evars)
      in
      let evars' = List.map (fun (_,x) -> Vars.EVar x) s in
      let isubst' =
        List.map
          (fun (i,i') -> i, Theory.var_i dum (Vars.name i'), i')
          s
        @ env_p.isubst
      in
      let env_p = { env_p with isubst = isubst' } in
      let cond' =
        Theory.subst cond (to_tsubst env_p.isubst @ to_tsubst env_p.msubst)
      in

      (* No state updates have been done yet in the current
       * action. We thus have to substitute [ts] by [pred(ts)] for all state
       * macros appearing in [t]. This is why we call [Term.subst_macros_ts]
       * with the empty list. *)
      let fact =
        Term.subst_macros_ts table [] (Term.mk_var ts)
          (conv_term table env_p (Term.mk_var ts) cond Type.Boolean)
      in
      let facts_p = fact :: env.facts in
      let facts_q =
        match evars' with
        | [] -> (Term.mk_not fact) :: env.facts
        | qvars -> 
          Term.mk_forall ~simpl:false qvars (Term.mk_not fact) :: env.facts
      in
      let env_p =
        { env_p with
          indices = List.rev_append (List.map snd s) env.indices ;
          isubst = isubst' ;
          evars = List.rev_append (List.map snd s) env.evars ;
          facts = facts_p }
      in
      let env_q = { env with facts = facts_q } in
      let p',pos_p,table = p_cond ~table ~env:env_p ~pos ~par_choice p in
      let q',pos_q,table = p_cond ~table ~env:env_q ~pos:pos_p ~par_choice q in

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
      let vars = List.rev env.evars in
      let env =
        { env with
          action = Action.{ par_choice ;
                            sum_choice = pos, vars } :: env.action }
      in
      let p',_,table = p_update_i ~table ~env proc in
      (p', pos + 1,table)


  and p_update ~table ~env (proc : process) =
    let p, pos, table = p_update_i ~table ~env proc in
    (L.mk_loc (L.loc proc) p, pos, table)

  and p_update_i ~table ~env (proc : process) =
    let loc = L.loc proc in
    match L.unloc proc with
    | Apply _ | Alias _ | New _ ->
      let table,env,p = p_common ~table ~env proc in
      p_update_i ~table ~env p

    | Let (x,t,ty,p) ->
      let x',t',table,env,p = p_let ~in_update:true ~table ~env proc in
      let p',pos',table = p_update ~table ~env p in
      let x' = L.mk_loc (L.loc x) (Symbols.to_string x') in

      ( Let (x', t',ty,p'),
        pos',
        table )

    | Set (s,l,t,p) ->
      if List.exists (fun (s',_,_,_) -> L.unloc s = L.unloc s') env.updates
      then
        (* Not allowed because a state macro can have only 2 values:
           - either the value at the end of the current action,
           - either the value before the current action.
             There is no in-between value. *)
        proc_err loc (DuplicatedUpdate (L.unloc s));

      let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
      let l' =
        List.map
          (fun i ->
             snd (list_assoc (L.unloc i) env.isubst))
          l
      in
      let updated_states =
        let apps = List.map (fun (s,_,_,_) -> L.unloc s) env.updates in
        Theory.find_app_terms t' apps            
      in
      let ty = Theory.check_state table s (List.length l) in
      let t'_tm =
        Term.subst_macros_ts table updated_states (Term.mk_var ts)
          (conv_term table env (Term.mk_var ts) t ty)
      in
      let env =
        { env with updates = (s,l',ty,t'_tm) :: env.updates }
      in
      let p',pos',table = p_update ~table ~env p in

      (* we could re-use the location in [l] here. *)
      let l' = List.map (fun x -> mk_dum (Vars.name x)) l' in

      ( Set (s,l',t',p'),
        pos',
        table )

    | Out (c,t,p) ->
      let ch = Channel.of_lsymb c table in
      let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in

      let table,env,a' = register_action loc env.alias (Some (ch,t)) table env in
      let env =
        { env with
          evars = [] ;
          facts = [] ;
          updates = [] }
      in
      let p',pos',table = p_in ~table ~env ~pos:0 ~pos_indices:[] p in
      (* The same location re-used twice, as both sub-processes come from the
         same initial process. *)
      let p' = L.mk_loc loc (Out (c,t',p')) in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (p', a'),
        pos',
        table )

    | Null ->
      let table,env,a' = register_action loc env.alias None table env in
      let pnull = L.mk_loc loc Null in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (pnull, a'),
        0,
        table)

    | In _ | Parallel _ | Repl _ | Exists _ ->
      let table,env,a' = register_action loc env.alias None table env in
      let env =
        { env with
          evars = [] ;
          facts = [] ;
          updates = [] }
      in
      let p',pos',table = p_in ~table ~env ~pos:0 ~pos_indices:[] proc in

      let c_dummy = Symbols.dummy_channel_lsymb in

      let p'_i = Out (c_dummy, Theory.empty dum,p') in
      let p' = L.mk_loc loc p'_i in
      let a' = mk_dum (Symbols.to_string a') in

      ( Alias (p', a'),
        pos',
        table )

  in

  let env =
    { ty_env   = Type.Infer.mk_env ();
      alias    = L.mk_loc L._dummy "A" ;
      indices  = [] ;
      vars_env = env_ts ;
      isubst   = [] ;
      msubst   = [] ;
      inputs   = [] ;
      evars    = [] ;
      action   = [] ;
      facts    = [] ;
      updates  = [];
      globals  = []; }
  in

  let proc,_,table = p_in ~table:init_table ~env ~pos:0 ~pos_indices:[] proc in

  (* I believe this test is not useful *)
  if not (Type.Infer.is_closed env.ty_env) then 
    proc_err (L.loc proc) Freetyunivar;

  (proc, table)

let declare_system table (system_name : lsymb) proc =
  Printer.pr "@[<v 2>Un-processed system:@;@;@[%a@]@]@.@." pp_process proc ;
  check_proc table Vars.empty_env proc ;
  let table, system_name = System.declare_empty table system_name in

  (* before parsing the system, we register the init action,
  using for the updates the initial values declared when declaring
  a mutable construct *)
  let a' = Symbols.init_action in
  let updates = Theory.get_init_states table in
  let action_descr = Action.{ 
      name      = a';
      action    = [];
      input     = (Symbols.dummy_channel,"$dummyInp");
      indices   = [];
      condition = ([], Term.mk_true);
      updates;
      output    = (Symbols.dummy_channel, Term.empty);
      globals   = []; }
  in
  let table, _, _ =
    System.register_action table system_name a' [] [] action_descr
  in

  let proc,table = parse_proc system_name table proc in
  Printer.pr "@[<v 2>Processed system:@;@;@[%a@]@]@.@." pp_process proc ;
  Printer.pr "%a" System.pp_systems table;
  table
