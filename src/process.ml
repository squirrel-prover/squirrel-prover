type pkind = (string * Sorts.esort) list

type id = string

type term = Theory.term
type formula = Theory.formula

(* TODO add parsing positions *)
type process =
  | Null
  | New of string * process
  | In of Channel.t * string * process
  | Out of Channel.t * term * process
  | Set of string * string list * term * process
  | Parallel of process * process
  | Let of string * term * process
  | Repl of string * process
  | Exists of string list * formula * process * process
  | Apply of id * term list
  | Alias of process * id

let rec pp_process ppf process =
  let open Fmt in
  let open Utils in
  match process with
  | Null ->  (styled `Blue (styled `Bold ident)) ppf "null"

  | Apply (s,l) ->
      pf ppf "@[<hov>%a@ %a@]"
        (styled `Bold (styled `Blue ident)) s
        (Fmt.list ~sep:(fun ppf () -> pf ppf "@ ") Theory.pp) l

  | Alias (p,a) ->
      pf ppf "@[%s:@ %a@]"
        a
        pp_process p

  | Repl (s, p) ->
    pf ppf "@[<hov 2>!_%s@ @[%a@]@]"
      s pp_process p

  | Set (s, indices, t, p) ->
    pf ppf "@[<hov>%s%a %a@ %a;@ @[%a@]@]"
      s
      (Utils.pp_list Fmt.string) indices
      (kw `Bold) ":="
      Theory.pp t
      pp_process p

  | New (s, p) ->
    pf ppf "@[<hov>%a %a;@ @[%a@]@]"
      (kw `Red) "new"
      (kw `Magenta) s
      pp_process p

  | In (c, s, p) ->
    pf ppf "@[<hov>%a(%a,@,%a);@ %a@]"
      (kw `Bold) "in"
      Channel.pp_channel c
      (styled `Magenta (styled `Bold ident)) s
      pp_process p

  | Out (c, t, p) ->
    pf ppf "@[<hov>%a(%a,@,%a);@ %a@]"
      (kw `Bold) "out"
      Channel.pp_channel c
      Theory.pp t
      pp_process p

  | Parallel (p1, p2) ->
    pf ppf "@[<hv>@[(%a)@] |@ @[(%a)@]@]"
      pp_process p1
      pp_process p2

  | Let (s, t, p) ->
    pf ppf "@[<v>@[<2>%a %a =@ @[%a@] %a@]@ %a@]"
      (kw `Bold) "let"
      (styled `Magenta (styled `Bold ident)) s
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
        (Utils.pp_list Fmt.string) ss
        (styled `Red (styled `Underline ident)) "such that"
        Theory.pp f
        (styled `Red (styled `Underline ident)) "in"
        pp_process p1 ;
    if p2 <> Null then
      pf ppf "@ %a@;<1 2>%a@]"
      (styled `Red (styled `Underline ident)) "else"
      pp_process p2
    else
      pf ppf "@]"


(** Table of declared (bi)processes with their types.
  * TODO use Symbols ? *)
let pdecls : (string,pkind*process) Hashtbl.t = Hashtbl.create 97

(** Type checking for processes *)
let rec check_proc env = function
  | Null -> ()
  | New (x, p) -> check_proc ((x, Sorts.emessage)::env) p
  | In (_,x,p) -> check_proc ((x, Sorts.emessage)::env) p
  | Out (_,m,p) ->
    Theory.check ~local:true env m Sorts.emessage ;
    check_proc env p
  | Set (s, l, m, p) ->
    let k = Theory.check_state s (List.length l) in
    Theory.check ~local:true env m k ;
    List.iter
      (fun x ->
         Theory.check ~local:true env (Theory.Var x) Sorts.eindex) l ;
    check_proc env p
  | Parallel (p, q) -> check_proc env p ; check_proc env q
  | Let (x, t, p) ->
    Theory.check ~local:true env t Sorts.emessage ;
    check_proc ((x, Sorts.emessage)::env) p
  | Repl (x, p) -> check_proc ((x, Sorts.eindex)::env) p
  | Exists (vars, test, p, q) ->
    check_proc env q ;
    let env =
      List.rev_append
        (List.map (fun x -> x, Sorts.eindex) vars)
        env
    in
    Theory.check ~local:true env test Sorts.eboolean ;
    check_proc env p
  | Apply (id, ts) ->
    begin
      try
        let kind,_ = Hashtbl.find pdecls id in
        if List.length kind <> List.length ts then
          raise @@
          Theory.(Conv (Arity_error (id, List.length ts, List.length kind)));
        List.iter2
          (fun (_, k) t -> Theory.check ~local:true env t k)
          kind ts
      with
      | Not_found -> raise @@ Theory.(Conv (Undefined id))
    end
  | Alias (p,_) -> check_proc env p

let declare id args proc =
  if Hashtbl.mem pdecls id then raise @@ Symbols.Multiple_declarations id;
  check_proc args proc ;
  Hashtbl.add pdecls id (args, proc)

exception Cannot_parse of process

type p_env = {
  (* RELATED TO THE CURRENT PROCESS *)
  alias : string ;
    (* alias for this process *)
  indices : Vars.index list ;
    (* bound indices *)
  vars_env : Vars.env ref ;
    (* local variables environment *)
  isubst : (string * Theory.term * Vars.index) list ;
    (* substitution for index variables (Repl, Exists, Apply) *)
  msubst : (string * Theory.term * Term.message) list ;
    (* substitution for message variables (New, Let, In, Apply) *)
  inputs : (Channel.t * Vars.message) list ;
    (* bound input variables *)
  (* RELATED TO THE CURRENT ACTION *)
  evars : Vars.index list ;
  (* variables bound by existential quantification *)
  action : Action.action ;
    (* the type [Action.action] describes the execution point in the protocol *)
  facts : Term.formula list ;
    (* list of formulas to create the condition term of the action *)
  updates : (string * string list * Term.message) list ;
    (* list of updates performed in the action *)
  local_macros : string list
    (* list of local macros defined in the action *)
}

let parse_proc system_name proc =
  let env_ts,ts = Vars.make_fresh Vars.empty_env Sorts.Timestamp "ts" in

  (* Convert a Theory.term to Term.term using the special sort
   * of substitution maintained by the parsing function. *)
  let create_subst isubst msubst =
    (List.map
      (fun (x,_,tm) ->
         match tm with
           | v -> Theory.ESubst (x,Term.Var v)
           (* |  _ -> assert false *)
       )
      isubst)
    @
    (List.map
      (fun (x,_,tm) -> Theory.ESubst (x,tm))
      msubst)
  in
  let conv_term ?(pred=true) env dep ts t sort =
    let subst = create_subst env.isubst env.msubst in
    if pred
    then
      let t' = Theory.convert ~at:(Term.Pred ts) subst t sort in
      if List.length dep > 0
      then
        Term.subst_macros_ts dep (Term.Pred ts) ts t'
      else
        t'
    else
      Theory.convert ~at:ts subst t sort
  in
  let conv_indices env l =
    List.map
      (fun x ->
        List.assoc x
          (List.map (fun (x,_,z) -> x,z) env.isubst))
      l
  in

  let list_assoc v l =
    let _,th,tm = List.find (fun (x,_,_) -> x = v) l in
    th,tm
  in
  let to_tsubst subst = List.map (fun (x,y,_) -> x,y) subst in

  let register_action a output env =
    let _,a' = Action.fresh_symbol Symbols.dummy_table a in
    let action = List.rev env.action in
    let input = match env.inputs with
    | [] -> (Channel.dummy, "_")
    | (c,v)::_ -> (c,Vars.name v)
    in
    let indices = List.rev env.indices in
    let action_term = Term.Action (a', indices) in
    let subst_ts = [Term.ESubst (Term.Var ts, action_term)] in
    let condition =
      List.rev env.evars,
      Term.subst subst_ts (List.fold_left Term.mk_and Term.True env.facts)
    in
    let updates =
      List.map
        (fun (s,l,t) ->
          (Symbols.Macro.of_string s, Sorts.Message, conv_indices env l),
           Term.subst subst_ts t)
        env.updates
    in
    let output = match output with
      | Some (c,t) -> c, conv_term ~pred:false env [] action_term t Sorts.Message
      | None -> Channel.dummy, Term.dummy
    in
    let action_descr =
      Action.{ action; input; indices; condition; updates; output } in
    let _,new_a =
      Action.register
        Symbols.dummy_table
        system_name a' indices action action_descr
    in
    (env, new_a)
  in

  let p_common ~env proc = match proc with

  | Apply (id,args) | Alias (Apply (id,args), _) ->
    (* Keep explicit alias if there is one,
     * otherwise use id as the new alias. *)
    let a' = match proc with Alias (_,a) -> a | _ -> id in
    let t,p = Hashtbl.find pdecls id in
    let isubst', msubst' =
      (* TODO avoid or handle conflicts with variables already
       * in domain of subst, i.e. variables bound above the apply *)
      let tsubst = (to_tsubst env.isubst@to_tsubst env.msubst) in
      List.fold_left2
        (fun (iacc,macc) (x,k) v ->
          match k,v with
          | Sorts.ESort Sorts.Message,_ ->
            let v' = Theory.subst v tsubst in
            iacc, (x, v', conv_term env [] (Term.Var ts) v' Sorts.Message)::macc
          | Sorts.ESort Sorts.Index, Theory.Var i ->
            let _,i' = list_assoc i env.isubst in
            (x, Theory.subst v tsubst, i')::iacc, macc
          | _ -> assert false)
        (env.isubst,env.msubst) t args
    in
    let env =
    { env with
      alias = a' ;
      isubst = isubst' ;
      msubst = msubst' }
    in
    (env,p)

  | New (n,p) ->
    (* TODO getting a globally fresh symbol for the name
     * does not prevent conflicts with variables bound in
     * the process (in Repl, Let, In...) *)
    let _,n' =
      Symbols.Name.declare Symbols.dummy_table n (List.length env.indices) in
    let n'_th =
      Theory.Name
        (Symbols.to_string n',
         List.rev_map (fun i -> Theory.Var (Vars.name i)) env.indices)
    in
    let n'_tm = Term.Name (n',List.rev env.indices) in
    let env =
    { env with
      msubst = (n,n'_th,n'_tm) :: env.msubst }
    in
    (env,p)

  | _ -> assert false

  in

  let rec p_in ~env ~pos ~pos_indices proc = match proc with
  | Null -> (Null,pos)

  | Parallel (p,q) ->
    let current_env = !(env.vars_env) in
    let env =
      { env with
        vars_env = ref current_env }
    in
    let p',pos_p = p_in ~env ~pos ~pos_indices p in
    let q',pos_q = p_in ~env ~pos:pos_p ~pos_indices q in
    (Parallel (p',q'), pos_q)

  | Repl (i,p) ->
    let i' = Vars.make_fresh_and_update env.vars_env Sorts.Index i in
    let env =
      { env with
        isubst = (i, Theory.Var (Vars.name i'), i') :: env.isubst ;
        indices = i' :: env.indices }
    in
    let pos_indices = i'::pos_indices in
    let p',pos' = p_in ~env ~pos ~pos_indices p in
    (Repl (Vars.name i', p'),pos')

  | Apply (id,args) | Alias (Apply (id,args), _) ->
    let env,p = p_common env proc in
    p_in ~env ~pos ~pos_indices p

  | New (n,p) ->
    let env,p = p_common env proc in
    p_in ~env ~pos ~pos_indices p

  | Let (x,t,p) ->
    let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
    let dep = Theory.find_fun_terms t' env.local_macros in
    let body = conv_term env dep (Term.Var ts) t' Sorts.Message in
    let invars = List.map snd env.inputs in
    let _,x' =
      Macros.declare_global Symbols.dummy_table x ~inputs:invars
        ~indices:(List.rev env.indices) ~ts:ts body
    in
    let x'_th =
      Theory.Fun
        (Symbols.to_string x',
         List.rev_map (fun i -> Theory.Var (Vars.name i)) env.indices,
         None)
    in
    let x'_tm =
      Term.Macro ((x', Sorts.Message, List.rev env.indices), [],
                  Term.Var ts)
    in
    let env =
      { env with
        msubst = (x,x'_th,x'_tm) :: env.msubst ;
        local_macros = (Symbols.to_string x')::env.local_macros }
    in
    let p',pos' = p_in ~env ~pos ~pos_indices p in
    (Let (Symbols.to_string x', t', p'),pos')

  | In (c,x,p) ->
    let x' = Vars.make_fresh_and_update env.vars_env Sorts.Message x in
    let in_th =
      Theory.Fun (Vars.name x', [], None)
    in
    let in_tm =
      Term.Macro (Term.in_macro, [], Term.Var ts) in
    let env =
      { env with
        inputs = (c,x')::env.inputs ;
        msubst = (Vars.name x', in_th, in_tm) :: env.msubst }
    in
    let par_choice = pos, List.rev pos_indices in
    let p',_ = p_cond ~env ~pos:0 ~par_choice p in
    (In (c,Vars.name x',p'), pos+1)

  | Exists _ | Set _ | Alias _ | Out _ ->
    let par_choice = pos, List.rev pos_indices in
    let p',_ = p_cond ~env ~pos:0 ~par_choice proc in
    (p', pos+1)

  and p_cond ~env ~pos ~par_choice proc = match proc with
  | Apply (id,args) | Alias (Apply (id,args), _) ->
    let env,p = p_common env proc in
    p_cond ~env ~pos ~par_choice p

  | New (n,p) ->
    let env,p = p_common env proc in
    p_cond ~env ~pos ~par_choice p

  | Let (x,t,p) ->
    let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
    let dep = Theory.find_fun_terms t' env.local_macros in
    let body = conv_term env dep (Term.Var ts) t' Sorts.Message in
    let invars = List.map snd env.inputs in
    let _,x' =
      Macros.declare_global Symbols.dummy_table x ~inputs:invars
        ~indices:(List.rev env.indices) ~ts:ts body
    in
    let x'_th =
      Theory.Fun
        (Symbols.to_string x',
         List.rev_map (fun i -> Theory.Var (Vars.name i)) env.indices,
         None)
    in
    let x'_tm =
      Term.Macro ((x', Sorts.Message, List.rev env.indices), [],
                  Term.Var ts)
    in
    let env =
      { env with
        msubst = (x,x'_th,x'_tm) :: env.msubst ;
        local_macros = (Symbols.to_string x')::env.local_macros }
    in
    let p',pos' = p_cond ~env ~pos ~par_choice p in
    (Let (Symbols.to_string x', t', p'),pos')

  | Exists (evars, cond, p, q) ->
    let s =
      List.fold_left
        (fun s i ->
          let i' = Vars.make_fresh_and_update env.vars_env Sorts.Index i in
          (i,i')::s)
        []
        (List.rev evars)
    in
    let evars' = List.map (fun (_,x) -> Vars.EVar x) s in
    let isubst' =
      List.map
        (fun (i,i') -> i, Theory.Var (Vars.name i'), i')
        s
      @ env.isubst
    in
    let cond' = Theory.subst cond (to_tsubst isubst' @ to_tsubst env.msubst) in
    let dep = Theory.find_fun_terms cond' env.local_macros in
    let fact = conv_term env dep (Term.Var ts) cond' Sorts.Boolean in
    let facts_p = fact::env.facts in
    let facts_q =
      match evars' with
      | [] -> (Term.Not fact) :: env.facts
      | qvars -> (Term.ForAll(qvars, Term.Not fact)) :: env.facts
    in
    let env_p =
      { env with
        indices = List.rev_append (List.map snd s) env.indices ;
        isubst = isubst' ;
        evars = List.rev_append (List.map snd s) env.evars ;
        facts = facts_p }
    in
    let env_q =
      { env with
        indices = List.rev_append (List.map snd s) env.indices ;
        isubst = isubst' ;
        facts = facts_q }
    in
    let p',pos_p =
      p_cond ~env:env_p ~pos ~par_choice p
    in
    let q',pos_q =
      p_cond ~env:env_q ~pos:pos_p ~par_choice q
    in

    (Exists (List.map (fun (_,x) -> Vars.name x) s,cond',p',q'), pos_q)

  | p ->
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
    let p',_ = p_update ~env p in
    (p', pos + 1)

  and p_update ~env proc = match proc with
  | Apply (id,args) | Alias (Apply (id,args), _) ->
    let env,p = p_common env proc in
    p_update ~env p

  | New (n,p) ->
    let env,p = p_common env proc in
    p_update ~env p

  | Let (x,t,p) ->
    let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
    let states_already_updated = (List.map (fun (s,_,_) -> s) env.updates) in
    let dep =
      (Theory.find_fun_terms t' env.local_macros)
      @ (Theory.find_get_terms t' states_already_updated)
    in
    let body = conv_term env dep (Term.Var ts) t' Sorts.Message in
    let invars = List.map snd env.inputs in
    let _,x' =
      Macros.declare_global Symbols.dummy_table x ~inputs:invars
        ~indices:(List.rev env.indices) ~ts:ts body
    in
    let x'_th =
      Theory.Fun
        (Symbols.to_string x',
         List.rev_map (fun i -> Theory.Var (Vars.name i)) env.indices,
         None)
    in
    let x'_tm =
      Term.Macro ((x', Sorts.Message, List.rev env.indices), [],
                  Term.Var ts)
    in
    let env =
      { env with
        msubst = (x,x'_th,x'_tm) :: env.msubst ;
        local_macros = (Symbols.to_string x')::env.local_macros }
    in
    let p',pos' = p_update ~env p in
    (Let (Symbols.to_string x', t', p'),pos')

  | Set (s,l,t,p) ->
    if List.exists (fun (s',_,_) -> s=s') env.updates
    then
      (* Not allowed because a state macro can have only 2 values:
         - either the value at the end of the current action,
         - either the value before the current action.
         There is no in-between value. *)
      failwith "Cannot update twice the same state in an action"
      (* FIXME handle this in check_proc ? *)
    else
      let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
      let l' =
        List.map
          (fun i ->
             match list_assoc i env.isubst with
               | Theory.Var i',_ -> i'
               | _ -> assert false)
          l
      in
      let states_already_updated = (List.map (fun (s,_,_) -> s) env.updates) in
      let dep =
        (Theory.find_fun_terms t' env.local_macros)
        @ (Theory.find_get_terms t' states_already_updated)
      in
      let t'_tm = conv_term env dep (Term.Var ts) t' Sorts.Message in
      let env =
        { env with
          updates = (s,l',t'_tm)::env.updates }
      in
      let p',pos' = p_update ~env p in
      (Set (s,l',t',p'),pos')

  | Alias (Out (c,t,p),a) ->
    let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
    let env,a' = register_action a (Some (c,t')) env in
    let env =
      { env with
        evars = [] ;
        facts = [] ;
        updates = [] ;
        local_macros = [] }
    in
    let p',pos' = p_in ~env ~pos:0 ~pos_indices:[] p in
    (Alias (Out (c,t',p'), Symbols.to_string a'), pos')

  | Out (c,t,p) ->
    let t' = Theory.subst t (to_tsubst env.isubst @ to_tsubst env.msubst) in
    let env,a' = register_action env.alias (Some (c,t')) env in
    let env =
      { env with
        evars = [] ;
        facts = [] ;
        updates = [] ;
        local_macros = [] }
    in
    let p',pos' = p_in ~env ~pos:0 ~pos_indices:[] p in
    (Alias (Out (c,t',p'), Symbols.to_string a'), pos')

  | Null ->
    let env,a' = register_action "A" None env in
    let env =
      { env with
        evars = [] ;
        facts = [] ;
        updates = [] ;
        local_macros = [] }
    in
    let p',pos' = p_in ~env ~pos:0 ~pos_indices:[] proc in
    (Null, pos')

  | p -> raise (Cannot_parse p)

  in

  let env =
    { alias = "A" ;
      indices = [] ;
      vars_env = ref env_ts ;
      isubst = [] ;
      msubst = [] ;
      inputs = [] ;
      evars = [] ;
      action = [] ;
      facts = [] ;
      updates = [] ;
      local_macros = [] }
  in
  let proc,_ = p_in ~env ~pos:0 ~pos_indices:[] proc in
  (proc, Symbols.dummy_table)


(* FIXME table unused ? cf utilisation de Symbols.dummy_table ? *)
let declare_system table (system_name:Action.system_name) proc =
  if not(Action.is_fresh system_name) then
    failwith "System %s already defined";
  Printer.pr "@[<v 2>Un-processed system:@;@;@[%a@]@]@.@." pp_process proc ;
  check_proc [] proc ;
  let proc,table = parse_proc system_name proc in
  Printer.pr "@[<v 2>Pre-processed system:@;@;@[%a@]@]@.@." pp_process proc ;
  table

let reset () =
  Hashtbl.clear pdecls ;
  Action.reset ()
