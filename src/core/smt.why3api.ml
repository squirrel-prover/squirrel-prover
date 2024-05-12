open Utils

let smt_debug = Sys.getenv_opt "SMT_DEBUG" <> None

(** Style for translating timestamps. *)
type timestamp_style =
  | Abstract     (** Abstract with specific ~~ for comparison. *)
  | Abstract_eq  (** Abstract with builtin equality for comparison. *)
  | Nat          (** Natural numbers. *)

let start_timer () =
  let t0 = Unix.gettimeofday () in
  fun () -> Unix.gettimeofday () -. t0
    
let config = Why3.Whyconf.init_config None

let main = Why3.Whyconf.get_main config

let why3_provers = Why3.Whyconf.get_provers config

let env = 
  let exec_dir = Filename.dirname Sys.executable_name in
  Why3.Env.create_env
    (Filename.(concat exec_dir "theories") ::
    Why3.Whyconf.(loadpath (get_main config)))

let load_theory ~timestamp_style ~pure env = 
  try 
    let theory = (if pure then "pure_" else "")^
                  "trace_model"^
                  (match timestamp_style with 
                    |Abstract -> "_abs" | Abstract_eq -> "_abs_eq" | _ ->"") in
    Some (Why3.Env.read_theory env [theory] (String.capitalize_ascii theory))
  with
    | Why3.Env.LibraryConflict _ | Why3.Env.LibraryNotFound _
    | Why3.Env.AmbiguousPath   _ | Why3.Env.TheoryNotFound  _ ->
      Format.printf "SMT: error while loading SMT theory file\n"; None

let create_call ?limit_opt prover table config_prover task :
  Why3.Call_provers.prover_call option =
  let limit = match limit_opt with
    | None   -> TConfig.solver_timeout (table)
    | Some x -> x
  in
  Format.eprintf
    "Creating prover task for %s (version:%s altern:%S)...@."
    prover.Why3.Whyconf.prover_name
    prover.Why3.Whyconf.prover_version
    prover.Why3.Whyconf.prover_altern;
  try
    let driver =
      Why3.Driver.load_driver_for_prover
        main
        env
        config_prover
    in
    let limit =
      { Why3.Call_provers.empty_limit with limit_time = float_of_int limit }
    in
    Some
      (Why3.Driver.prove_task
        ~config:main
        ~command:config_prover.command
        ~limit
        driver
        task)
  with e ->
    Format.printf
      "SMT: %s driver failed to load: %a@.\n"
      prover.Why3.Whyconf.prover_name Why3.Exn_printer.exn_printer e;
      None

let run_all_async ~slow ~provers table task =
  Why3.Prove_client.set_max_running_provers 4;
  let timer = start_timer () in
  let calls :
    (Why3.Whyconf.prover*Why3.Call_provers.prover_call)
    Why3.Whyconf.Mprover.t
  =
    Why3.Whyconf.Mprover.mapi_filter
      (fun p config_prover ->
        if List.mem Why3.Whyconf.(p.prover_name,p.prover_altern) provers then
          let call =
            if slow
            then create_call ~limit_opt:60 p table config_prover task
            else create_call p table config_prover task
          in
          match call with
          | Some call -> Some (p,call)
          | None -> None
        else None)
      why3_provers
  in
  if Why3.Whyconf.Mprover.is_empty calls then
    Format.printf "No available prover among specified options!@.";
  (* Number of calls for which we still need a result. *)
  let n = ref @@ Why3.Whyconf.Mprover.cardinal calls in
  if smt_debug then Format.eprintf "Waiting for new results...@.";
  let res = ref false in
  while !n>0 && not !res do
    let results = Why3.Call_provers.get_new_results ~blocking:true in
    if smt_debug then
      Format.printf
        "%d result(s) obtained after %.2fs.@."
        (List.length results)
        (timer ());
    List.iter
      (fun (prover_call,prover_update) ->
         match prover_update with
         | Why3.Call_provers.ProverFinished r ->
           decr n;
           Why3.Whyconf.Mprover.iter
             (fun prover (_,call) ->
                if call = prover_call then
                  Format.eprintf
                    "Prover %s (version:%s altern:%S) finished.@."
                    prover.Why3.Whyconf.prover_name
                    prover.Why3.Whyconf.prover_version 
                    prover.Why3.Whyconf.prover_altern)
             calls;
           Format.eprintf
             "Result: @[%a.@]@."
             (Why3.Call_provers.print_prover_result ~json:false)
            r;
           res := !res || (r.pr_answer = Why3.Call_provers.Valid)
         | _ -> if smt_debug then Format.eprintf "Other@.")
      results
  done;
  if smt_debug then
    Format.printf "Finished in %.2fs.@." (timer ());
  (* Interrupt remaining calls. *)
  Why3.Whyconf.Mprover.iter
    (fun _ (_,c) -> Why3.Call_provers.interrupt_call ~config:main c) calls;
  !res
  
(** Context for SMT translation, providing information on:
    - the Squirrel formulas being translated (e.g. table, system expression);
    - the SMT formulas (declared symbols and variables);
    - the translation mode. *)
type context = { 
  table : Symbols.table;
  system : SystemExpr.fset option;

  index_symb : Why3.Ty.tysymbol;
  msg_symb : Why3.Ty.tysymbol option;
  ts_symb : Why3.Ty.tysymbol;
  eqv_symb : Why3.Term.lsymbol option;
  leq_symb : Why3.Term.lsymbol;
  happens_symb : Why3.Term.lsymbol;
  init_symb : Why3.Term.lsymbol;
  pred_symb : Why3.Term.lsymbol;
  xor_symb : Why3.Term.lsymbol option;
  macro_cond_symb : Why3.Term.lsymbol option;
  macro_exec_symb : Why3.Term.lsymbol option;
  empty_symb : Why3.Term.lsymbol option;
  pair_symb : Why3.Term.lsymbol option;
  fst_symb : Why3.Term.lsymbol option;
  snd_symb : Why3.Term.lsymbol option;
  att_symb : Why3.Term.lsymbol option;
  of_bool_symb : Why3.Term.lsymbol option;
  input_symb : Why3.Term.lsymbol option;
  output_symb : Why3.Term.lsymbol option;
  frame_symb : Why3.Term.lsymbol option;
  msg_ty : Why3.Ty.ty option;
  ts_ty : Why3.Ty.ty;
  index_ty : Why3.Ty.ty;

  indices : Vars.var list;
  tsvars : Vars.var list;
  msgvars : Vars.var list;

  actions_tbl : (string, Why3.Term.lsymbol * int) Hashtbl.t;
  vars_tbl : (int,Why3.Term.term) Hashtbl.t;
  functions_tbl : (string, Why3.Term.lsymbol) Hashtbl.t;
  macros_tbl : (string, Why3.Term.lsymbol) Hashtbl.t;
  names_tbl : (string, Why3.Term.lsymbol) Hashtbl.t;
  unsupp_tbl : (Term.term*int, Why3.Term.lsymbol) Hashtbl.t;

  uc : Why3.Theory.theory_uc ref;

  timestamp_style : timestamp_style;
  pure : bool;
  fresh : int ref;
}

let filter_ty t = List.filter (fun x -> Vars.ty x = t)
let filter_msg = List.filter (fun x -> let t = Vars.ty x in
                                t <> Type.Index && t <> Type.Timestamp)

let id_fresh context name = 
  context.fresh:=!(context.fresh)+1;
  Why3.Ident.id_fresh (name^(string_of_int !(context.fresh)))

let mk_const_symb context x ty =
  Why3.Term.create_fsymbol (id_fresh context x) [] (ty)

exception InternalError

let context_init ~timestamp_style ~pure tm_theory evars table system = 
  let tm_export = tm_theory.Why3.Theory.th_export 
  and none_if_pure why3find tm symb = if pure then None 
                                      else Some (why3find tm symb) in 
  let index_symb = Why3.Theory.ns_find_ts tm_export ["index"]
  and msg_symb = none_if_pure Why3.Theory.ns_find_ts tm_export ["message"]
  and ts_symb = Why3.Theory.ns_find_ts tm_export ["timestamp"]
  and uc = ref (Why3.Theory.use_export 
    (Why3.Theory.create_theory (Why3.Ident.id_fresh "MyTheory")) 
    tm_theory
  )
  in 
  {
    table = table;
    system = system;
    index_symb   = index_symb;
    msg_symb     = msg_symb;
    ts_symb      = ts_symb;
    eqv_symb     =  if (timestamp_style=Abstract_eq) then None 
                    else Some (Why3.Theory.ns_find_ls tm_export ["infix ~~"]); 
    leq_symb     = Why3.Theory.ns_find_ls tm_export ["infix <~"];
    happens_symb = Why3.Theory.ns_find_ls tm_export ["happens"];
    init_symb    = Why3.Theory.ns_find_ls tm_export ["init"];
    pred_symb    = Why3.Theory.ns_find_ls tm_export ["pred"];
    xor_symb     = none_if_pure Why3.Theory.ns_find_ls tm_export ["xoxo"];
    macro_cond_symb  = none_if_pure 
                        Why3.Theory.ns_find_ls tm_export ["macro_cond"];
    macro_exec_symb  = none_if_pure 
                        Why3.Theory.ns_find_ls tm_export ["macro_exec"];
    empty_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["empty"];
    pair_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["pair"];
    fst_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["fst"];
    snd_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["snd"];
    att_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["att"];
    of_bool_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["of_bool"];
    input_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["input"];
    output_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["output"];
    frame_symb = none_if_pure Why3.Theory.ns_find_ls tm_export ["frame"];

    msg_ty   = if pure then None else 
        Some (Why3.Ty.ty_app (Option.get msg_symb) []);
    ts_ty    = Why3.Ty.ty_app ts_symb [];
    index_ty = Why3.Ty.ty_app index_symb [];

    indices = filter_ty Type.Index evars;
    tsvars = filter_ty Type.Timestamp evars;
    msgvars = filter_msg evars;
    actions_tbl = Hashtbl.create 12;
    vars_tbl = Hashtbl.create 193;
    functions_tbl = Hashtbl.create 12;
    macros_tbl = Hashtbl.create 12;
    names_tbl = Hashtbl.create 12;
    unsupp_tbl = Hashtbl.create 12;

    uc = uc;
    timestamp_style = timestamp_style;
    pure = pure;
    fresh = ref 0;
  }

(* Macro to use the correct equality depending on the theory *)
let ts_equ context t1 t2 = match context.timestamp_style with 
  | Abstract_eq -> Why3.Term.t_equ t1 t2 
  |_-> Why3.Term.t_app_infer (Option.get context.eqv_symb) [t1;t2]

let rec convert_type context = function
  | Type.Message -> (Option.get context.msg_ty)
  | Type.Timestamp -> context.ts_ty
  | Type.Boolean -> Why3.Ty.ty_bool 
  | Type.Tuple l -> Why3.Ty.ty_tuple (List.map (convert_type context) l)
  | Type.Index -> Why3.Ty.ty_app context.index_symb []
  | TBase t -> Why3.Ty.(ty_var (tv_of_string t))
  | TVar _ -> assert false 
  | Fun (t1,t2) -> Why3.Ty.ty_func (convert_type context t1)
                   (convert_type context t2)
  | TUnivar ty ->
    Format.printf
      "smt: unsupported argument type %a@."
      Type.pp (TUnivar ty);
    raise InternalError

(** {2 Translation} *)

open Why3.Term
let index_var_to_wterm context i = Hashtbl.find context.vars_tbl (Vars.hash i) 
let ilist_to_wterm_ts context l = List.map (index_var_to_wterm context) l 

let find_fn context f = Hashtbl.find context.functions_tbl (Symbols.to_string f)

let bool_to_prop t = 
  if Term.ty t = Type.Boolean then Why3.Term.to_prop else (fun x -> x)

let prop_to_bool p = Why3.Term.(t_if p t_bool_true t_bool_false) 
let rec prop_list_to_bool context terms = 
  List.map
    (fun (t,b) ->  if b then (prop_to_bool t) else t)
    (List.map 
      (fun t -> ((msg_to_fmla context) t, Term.ty t=Type.Boolean))
      terms
    )
   

and msg_to_fmla context : Term.term -> Why3.Term.term = fun fmla ->
  let open Term in
  let open Why3.Term in
  (bool_to_prop fmla) (match fmla,context.pure with 
    | Term.Var v,_ when Term.ty fmla = Type.Boolean -> 
      begin try to_prop (Hashtbl.find context.vars_tbl (Vars.hash v)) with
      | Not_found -> raise InternalError
      end
    | Term.Fun  (symb,_),_ -> begin match symb with 
      | _ when symb=f_false -> t_false
      | _ when symb=f_true ->  t_true
      | _ -> t_app_infer (find_fn context symb) []
    end
    | Term.App (Fun (symb,_),terms),_ ->  
      begin match terms with 
      | [f] when symb=f_not -> t_not (msg_to_fmla context f)
      | [f1;f2] when symb=f_and->
        t_and (msg_to_fmla context f1) (msg_to_fmla context f2)
      | [f1;f2] when symb=f_or ->
        t_or (msg_to_fmla context f1) (msg_to_fmla context f2)
      | [f1;f2] when symb=f_impl ->
        t_implies (msg_to_fmla context f1) (msg_to_fmla context f2)  
      | [f1;f2] when symb=f_iff -> 
        t_iff (msg_to_fmla context f1) (msg_to_fmla context f2)  
      | [f] when symb=f_pred -> 
        t_app_infer context.pred_symb [msg_to_fmla context f]
      | [t1;t2] when symb=f_xor -> 
        t_app_infer 
        (Option.get context.xor_symb)
          [msg_to_fmla context t1; 
          msg_to_fmla context t2]
      | [t1;t2] when symb = f_eq -> if Term.ty t1 = Type.Boolean then 
          t_iff (msg_to_fmla context t1) (msg_to_fmla context t2) 
          else 
            (if Term.ty t1 = Type.Timestamp then 
            ts_equ context (msg_to_fmla context t1) (msg_to_fmla context t2)
            else
            t_equ (msg_to_fmla context t1) (msg_to_fmla context t2) )
      | [t1;t2] when symb = f_neq -> if Term.ty t1 = Type.Boolean then 
        t_not (t_iff (msg_to_fmla context t1) (msg_to_fmla context t2)) 
        else 
          (if Term.ty t1 = Type.Timestamp then 
          t_not 
            (ts_equ context (msg_to_fmla context t1) (msg_to_fmla context t2))
          else
          t_not (t_equ (msg_to_fmla context t1) (msg_to_fmla context t2) ))
      | [t1;t2] when symb = f_leq -> assert (Term.ty t1 = Type.Timestamp);
        t_app_infer 
          context.leq_symb 
          [msg_to_fmla context t1;msg_to_fmla context t2]
      | [t1;t2] when symb = f_geq -> assert (Term.ty t1 = Type.Timestamp);
        t_app_infer 
          context.leq_symb 
          [msg_to_fmla context t2;msg_to_fmla context t1]
      | [t1;t2] when symb = f_lt -> assert (Term.ty t1 = Type.Timestamp);
            t_and 
              (t_app_infer 
                context.leq_symb
                [msg_to_fmla context t1;msg_to_fmla context t2]
              )
              (t_not @@ ts_equ context 
                (msg_to_fmla context t1) (msg_to_fmla context t2)
              )
      | [t1;t2] when symb = f_gt -> assert (Term.ty t1 = Type.Timestamp);
            t_and 
              (t_app_infer 
                context.leq_symb
                [msg_to_fmla context t2;msg_to_fmla context t1]
              )
              (t_not @@ ts_equ context 
                (msg_to_fmla context t2) (msg_to_fmla context t1)
              )
      | [t1] when symb = f_happens -> 
          t_app_infer context.happens_symb [msg_to_fmla context t1]
      | [cond;f1;f2] when symb=f_ite -> 
          t_if (msg_to_fmla context cond) 
            (msg_to_fmla context f1) 
            (msg_to_fmla context f2)
      | [_] when
          (Symbols.OpData.get_data symb context.table).ftype.fty_vars <> [] ->
        let var_list =
          Hashtbl.fold (fun _ x acc -> x::acc) context.vars_tbl [] in
        let symb =
          try
            Hashtbl.find context.unsupp_tbl (fmla, List.length var_list)
          with Not_found ->
            let s =
              Why3.Term.create_fsymbol
                  (id_fresh context "unsupp_poly")
                  (List.map t_type var_list)
                  (convert_type context (Term.ty fmla))
            in
            Hashtbl.add context.unsupp_tbl (fmla, List.length var_list) s;
            context.uc :=
              Why3.Theory.add_decl_with_tuples
                !(context.uc)
                (Why3.Decl.create_param_decl s);
            s
        in
        Why3.Term.t_app_infer symb var_list
      | _ -> 
        let f = find_fn context symb in 
        t_app_infer
          f 
          (prop_list_to_bool context terms)
      end
    | Term.Quant (ForAll, vs, f),_ -> msg_to_fmla_q context t_forall_close vs f
    | Term.Quant (Exists, vs, f),_ -> msg_to_fmla_q context t_exists_close vs f
    | Macro (ms,[],ts),false when ms.s_symb = Symbols.cond ->
      t_app_infer 
        (Option.get context.macro_cond_symb)
        [msg_to_fmla context ts]
    | Macro (ms,[],ts),false when ms.s_symb = Symbols.exec ->
      t_app_infer 
        (Option.get context.macro_exec_symb) 
        [msg_to_fmla context ts]
    | Action (a,indices),_ -> 
    (match indices with 
      |[Tuple ind_list] -> 
        t_app_infer (fst(Hashtbl.find context.actions_tbl (Symbols.to_string a))) 
        (List.map (msg_to_fmla context) ind_list)

      |_ -> 
        t_app_infer (fst(Hashtbl.find context.actions_tbl (Symbols.to_string a)))
        (List.map (msg_to_fmla context) indices)
      
    )
  | Macro (ms,l,ts),_ -> 
    (match l with 
      |[Tuple l_list] ->t_app_infer
        (Hashtbl.find context.macros_tbl (Symbols.to_string ms.s_symb))
        (List.map (msg_to_fmla context) l_list @
        [msg_to_fmla context ts])
      |_ ->t_app_infer
        (Hashtbl.find context.macros_tbl (Symbols.to_string ms.s_symb))
        (List.map (msg_to_fmla context) l @
        [msg_to_fmla context ts])
    )
    
  | Name (ns,args),_ ->
      (match args with 
      |[Tuple args_list] -> t_app_infer
        (Hashtbl.find context.names_tbl (Symbols.to_string ns.s_symb))
        (prop_list_to_bool context args_list)
      |_ -> t_app_infer
      (Hashtbl.find context.names_tbl (Symbols.to_string ns.s_symb))
      (prop_list_to_bool context args)
       
    )

  | Diff  _,_ | Find _,_ -> 
    let var_list = Hashtbl.fold (fun _ x acc -> x::acc) context.vars_tbl [] in
    let symb = try Hashtbl.find context.unsupp_tbl (fmla, List.length var_list) 
    with Not_found -> begin let s =  
      Why3.Term.create_fsymbol
          (id_fresh context "unsupp")
          (List.map t_type var_list)
          (convert_type context (Term.ty fmla))
      in Hashtbl.add context.unsupp_tbl (fmla, List.length var_list) s;
      context.uc := Why3.Theory.add_decl_with_tuples 
        !(context.uc) 
        (Why3.Decl.create_param_decl s);
      s 
      end
    in
    (Why3.Term.t_app_infer symb var_list)

  | Var v,_ -> 
    begin try Hashtbl.find context.vars_tbl (Vars.hash v) with
      | Not_found -> raise InternalError
    end

  | Tuple l,_ -> t_tuple (List.map (msg_to_fmla context) l)

  | _ -> assert false 
  )
and msg_to_fmla_q context quantifier vs f =
  let i_vs = filter_ty  Type.Index     vs
  and t_vs = filter_ty  Type.Timestamp vs
  and m_vs = filter_msg                vs in
  (* NOTE: here we use the fact that OCaml hashtables can have multiple
   *       bindings, and the newer ones shadow the older ones
   * thus we can use Hashtbl.(add|remove) to handle bound variable scope *)
  let create_var symb tbl v =
    let vsymb =
      create_vsymbol
        (id_fresh context (Vars.name v))
        (Why3.Ty.ty_app symb []) in
    Hashtbl.add tbl (Vars.hash v) (t_var vsymb);
    vsymb
  and rem_var tbl v = Hashtbl.remove tbl (Vars.hash v) in
  let quantified_vars =
    List.map (create_var context.index_symb context.vars_tbl) i_vs @
    List.map (create_var context.ts_symb context.vars_tbl) t_vs @
    (if context.pure then [] 
      else List.map 
        (create_var (Option.get context.msg_symb) context.vars_tbl)
        m_vs
    ) in
  (* at this stage the variables are added to the scope, we can recurse *)
  let subfmla = msg_to_fmla context f in
  (* and then cleanup *)
  List.iter (rem_var context.vars_tbl) i_vs;
  List.iter (rem_var context.vars_tbl) t_vs;
  (if not context.pure then List.iter (rem_var context.vars_tbl) m_vs);
  quantifier quantified_vars [] subfmla


(*Fill symbol tables*)
let add_actions context =
  SystemExpr.iter_descrs context.table (Option.get context.system)
    (fun descr ->
      if descr.name <> Symbols.init_action then
        let str = Symbols.to_string descr.name in
        let symb_act = Why3.Term.create_fsymbol
            (id_fresh context str)
            (List.init (List.length descr.indices) (fun _ -> context.index_ty))
            context.ts_ty
          in
          Hashtbl.add
            context.actions_tbl
            str
            (symb_act,List.length descr.indices));
  context.uc :=
    Hashtbl.fold
      (fun _ (symb,_) uc ->
         Why3.Theory.add_decl_with_tuples uc (Why3.Decl.create_param_decl symb))
      context.actions_tbl !(context.uc);
  Hashtbl.add
    context.actions_tbl
    Symbols.(to_string init_action)
    (context.init_symb,0)

let add_var context = 
  let add_tbl_var tbl ty uc var=
    let symb = mk_const_symb context (Vars.name var) ty in
    Hashtbl.add tbl (Vars.hash var) (Why3.Term.t_app_infer symb []);
    uc := Why3.Theory.add_decl_with_tuples !uc (Why3.Decl.create_param_decl symb)
  in
  List.iter 
    (add_tbl_var context.vars_tbl context.index_ty context.uc) 
    context.indices;
  List.iter 
    (add_tbl_var context.vars_tbl context.ts_ty context.uc) 
    context.tsvars;
  if (not context.pure) then (List.iter 
    (fun var -> 
      add_tbl_var 
        context.vars_tbl 
        (convert_type context (Vars.ty var))
        context.uc
        var
    ) 
    context.msgvars)

let add_functions context =
  Symbols.Operator.iter (fun fname _ ->
    let data = Symbols.OpData.get_data fname context.table in
    let ftype = data.ftype in
    let str = Symbols.to_string fname in
    (* special treatment of xor for two reasons:
     *   - id_fresh doesn't avoid the "xor" why3 keyword (why3 api bug?)
     *   - allows us to declare the equations for xor in the .why file *)
    let predeclared_symbols =
      [
        Symbols.fs_xor; Symbols.fs_pair;
        Symbols.fs_fst; Symbols.fs_snd;
        Symbols.fs_att; Symbols.fs_of_bool;
        Symbols.fs_empty; Symbols.fs_pred;
        Symbols.fs_happens; Symbols.fs_or;
        Symbols.fs_and; Symbols.fs_true;
        Symbols.fs_false; Symbols.fs_iff;
        Symbols.fs_impl; Symbols.fs_not;
        Symbols.fs_diff
      ]
    in
    if not (List.mem fname predeclared_symbols) then
      if ftype.Type.fty_vars <> [] then
        begin if smt_debug then
          Format.printf "Cannot declare %s : %a@." str Type.pp_ftype ftype
        end
      else begin
        let symb =
          Why3.Term.create_fsymbol
            (id_fresh context str)
            (List.map (convert_type context) ftype.fty_args)
            (convert_type context ftype.fty_out)
        in
        Hashtbl.add context.functions_tbl str (symb)
      end)
    context.table;
  context.uc :=
    Hashtbl.fold
      (fun _ (symb) uc ->
         Why3.Theory.add_decl_with_tuples uc
           (Why3.Decl.create_param_decl symb))
      context.functions_tbl !(context.uc);
  List.iter
    (fun (fname,symb) ->
       Hashtbl.add context.functions_tbl
         (Symbols.to_string fname)
         (symb))
    [(Symbols.fs_pair,(Option.get context.pair_symb));
     (Symbols.fs_fst,(Option.get context.fst_symb));
     (Symbols.fs_snd,(Option.get context.snd_symb));
     (Symbols.fs_att,(Option.get context.att_symb));
     (Symbols.fs_of_bool,(Option.get context.of_bool_symb));
     (Symbols.fs_empty,(Option.get context.empty_symb));
    ]


let add_macros context = 
  Symbols.Macro.iter (fun mn _ ->
    let def = Symbols.get_macro_data mn context.table in
    let str = Symbols.to_string mn in
    let indices = match def with
      | Input | Output | Cond | Exec | Frame -> 0
      | State (i,_,_) -> i
      | Global (i,_,_) -> i
    in
    let indices = List.init indices (fun _ -> context.index_ty) in
    let symb ty =
      Why3.Term.create_fsymbol
        (id_fresh context str)
        (indices @ [context.ts_ty])
        ty
    in
    match str with 
      |"exec" -> Hashtbl.add context.macros_tbl str 
                  (Option.get context.macro_exec_symb)
      |"cond" ->Hashtbl.add context.macros_tbl str 
                  (Option.get context.macro_cond_symb)
      |"input" ->Hashtbl.add context.macros_tbl str 
                  (Option.get context.input_symb)
      |"output" ->Hashtbl.add context.macros_tbl str 
                  (Option.get context.output_symb)
      |"frame" ->Hashtbl.add context.macros_tbl str
                  (Option.get context.frame_symb)
      |_ -> let ty = match def with 
        |State(_,t,_) | Global(_,t,_) -> convert_type context t 
        |_ -> assert false 
      in
      Hashtbl.add context.macros_tbl str (symb ty)
  ) context.table;
  context.uc:= Hashtbl.fold (fun _ (symb) uc ->
    begin try 
      Why3.Theory.add_decl_with_tuples uc (Why3.Decl.create_param_decl symb)
    with _ -> uc 
    end
    ) context.macros_tbl !(context.uc)

let rec calc_arity l = match l with 
  |[] -> 0
  |(Type.Tuple t)::q -> List.length t + (calc_arity q)
  | _::q -> 1 + (calc_arity q)

 let rec convert_type_no_tuple context t = match t with 
    |Type.Tuple l -> List.concat (List.map (convert_type_no_tuple context) l)
    |t -> [convert_type context t]

let add_names context = 
  Symbols.Name.iter (fun name _ ->
    let def = Symbols.get_name_data name context.table in
    let str = Symbols.to_string name in
    let symb =
      Why3.Term.create_fsymbol
        (id_fresh context str)
        (List.concat (List.map (convert_type_no_tuple context) 
        def.n_fty.fty_args))
        (convert_type context def.n_fty.fty_out)
      in
      Hashtbl.add context.names_tbl str (symb)

    
  ) context.table;
  context.uc:= Hashtbl.fold 
    (fun _ (symb) uc -> 
      Why3.Theory.add_decl_with_tuples uc (Why3.Decl.create_param_decl symb))
    context.names_tbl !(context.uc)
 
let rec vsymbol_list context c ty_list = match ty_list with 
  |[] -> []
  |t::q -> 
    (Why3.Term.create_vsymbol 
    (id_fresh context c) t)::(vsymbol_list context c q)
  
let rec equal_lists context tl1 tl2 = match tl1,tl2 with 
  |[],[] -> Why3.Term.t_true
  |[],_|_,[] -> Format.printf "Uneven arities@.";raise InternalError
  |h1::t1,h2::t2 -> match h1.t_ty with 
    |Some t when t=context.ts_ty -> Why3.Term.(t_and 
      (ts_equ context h1 h2) (equal_lists context t1 t2)) 
    |_ -> Why3.Term.(t_and (t_equ h1 h2) (equal_lists context t1 t2)) 
  
let add_timestamp_axioms context =  
  let distinct_actions_axioms = Hashtbl.fold (fun k (a,n) acc ->
    Hashtbl.fold (fun k' (a',n') acc' ->
        if k < k'
          then let l1,l2 = 
            vsymbol_list context "i" (List.init n (fun _ -> context.index_ty)),
            vsymbol_list context "j" (List.init n' (fun _ -> context.index_ty))
          in 
          let tl1,tl2 =
            List.map Why3.Term.t_var l1,List.map Why3.Term.t_var l2 
          in 
          Why3.Term.(t_forall_close l1 []
            (t_forall_close l2 [](
              t_implies 
                (t_app_infer context.happens_symb [t_app_infer a tl1]) (
                t_implies 
                  (t_app_infer context.happens_symb [t_app_infer a' tl2]) (
                  t_not 
                    ( ts_equ context (t_app_infer a tl1) (t_app_infer a' tl2))
            )))
          ))::acc'
          else acc'
    ) context.actions_tbl acc 
  ) context.actions_tbl [] 

  and injective_timestamps = 
    let axiom_injective_ts a n =
      let l1,l2 = 
        vsymbol_list context "i" (List.init n (fun _ -> context.index_ty)),
        vsymbol_list context "j" (List.init n (fun _ -> context.index_ty))
      in 
      let tl1,tl2 = List.map Why3.Term.t_var l1,List.map Why3.Term.t_var l2 in 
      Why3.Term.(t_forall_close l1 [](t_forall_close l2 [](
      t_implies (t_app_infer context.happens_symb [t_app_infer a tl1]) (
        t_implies (t_app_infer context.happens_symb [t_app_infer a tl2]) (
          t_implies (ts_equ context (t_app_infer a tl1) (t_app_infer a tl2)) (
            equal_lists context tl1 tl2
          )
        )
      )
      )))
    in

  Hashtbl.fold (fun _ (a,n) acc -> 
    (axiom_injective_ts a n)::acc
  ) context.actions_tbl []
  in
  (* RQ : = au lieu de ~~, c'est correct car on suppose que l'action happ, et ça permet de clore des buts*)
  (*Case disjunction for timestamps. TODO : only one version should remain*)
  (*First version : one axiom is generated for each timestamp variable*)
  let case_timestamps = 
    let axiom_case_ts t = 
      Why3.Term.t_implies (Why3.Term.t_app_infer context.happens_symb [t]) (
      Hashtbl.fold (fun _ (a,n) fml ->
        let l1 = 
          vsymbol_list context "i" (List.init n (fun _ -> context.index_ty)) 
        in let tl1 = List.map Why3.Term.t_var l1 in 
        Why3.Term.(t_or
          (t_exists_close l1 [](t_equ (t) (t_app_infer a tl1)))
          fml
        )
        ) context.actions_tbl (Why3.Term.t_false)
      )
    in
    Hashtbl.fold (fun _ t acc -> if t.Why3.Term.t_ty = Some(context.ts_ty)
        then (axiom_case_ts t)::acc
        else acc
      ) context.vars_tbl []
  in

  (*Second version : the axiom is universally quantified over timestamps*)
  let case_timestamp = 
    let t_vsymb = Why3.Term.create_vsymbol 
      (id_fresh context "t") 
      context.ts_ty 
    in 
    let t = Why3.Term.t_var t_vsymb in 
    Why3.Term.t_forall_close [t_vsymb] [] (
      Why3.Term.t_implies (Why3.Term.t_app_infer context.happens_symb [t]) (
      Hashtbl.fold (fun _ (a,n) fml ->
        let l1 = 
          vsymbol_list context "i" 
          (List.init n (fun _ -> context.index_ty)) 
        in let tl1 = List.map Why3.Term.t_var l1 in 
        Why3.Term.(t_or 
          (t_exists_close l1 [](t_equ (t) (t_app_infer a tl1) )) 
          fml
        )
        ) context.actions_tbl (Why3.Term.t_false)
      ))
  in

  (* Add axioms for action dependencies to above mutable list *)
  (* "depends" function from action.ml but weakened *)
  let depends = 
    SystemExpr.fold_descrs 
      (fun descr1 acc -> SystemExpr.fold_descrs (fun descr2 acc'->
        if descr1.name <> Symbols.init_action &&
          Action.depends
            (Action.get_shape_v descr1.action)
            (Action.get_shape_v descr2.action)
        then begin
          let action_indices = Hashtbl.create (List.length descr2.indices) in
          (* assume that all variables must occur in 2nd action *)
          let quantified_vars = descr2.indices |> List.map (fun i ->
              let vsymb =
                Why3.(Term.create_vsymbol
                        (Ident.id_fresh (Vars.name i))
                        (Ty.ty_app context.index_symb [])) in
              Hashtbl.add action_indices (Vars.hash i) vsymb;
              vsymb
            ) in
          let list_of_index_list (l : Vars.var list) : Why3.Term.term list =
            let open Why3.Term in
            List.fold_right (fun i acc ->
              (t_var (Hashtbl.find action_indices (Vars.hash i))):: acc) 
            l []
          in
          let f (d : Action.descr) =
            let symb = 
              fst (Hashtbl.find context.actions_tbl (Symbols.to_string d.name)) in
            let indices = List.take (List.length d.indices) descr2.indices in 
            Why3.Term.t_app_infer symb (list_of_index_list indices)
          in
          (* 1 <~ 2 **when 2 happens** *)
          let axiom = let open Why3.Term in
            t_app_infer context.leq_symb [f descr1; f descr2]
            |> t_implies (t_app_infer context.happens_symb [f descr2])
            |> t_forall_close quantified_vars [] in
          axiom::acc'
      end 
      else acc'
      ) context.table (Option.get context.system) acc
    ) 
    context.table (Option.get context.system) [] 
  in 
  context.uc:=List.fold_left 
    (fun acc (id_ax, ax) -> 
      Why3.Theory.add_decl_with_tuples acc 
      (Why3.Decl.create_prop_decl 
        Why3.Decl.Paxiom 
        (Why3.Decl.create_prsymbol @@ id_fresh context id_ax)
        ax
      )
    ) 
    !(context.uc) (List.map (fun x -> ("axiom_distinct", x)) 
                        (distinct_actions_axioms)
                        @ [("case_timestamp", case_timestamp)]
                        @ (List.map (fun x -> ("case_timsetamps", x))
                        case_timestamps) 
                        @ (List.map (fun x -> ("axiom_depends", x))
                        depends) 
                        @ (List.map (fun x -> ("axiom_injective", x))
                        injective_timestamps)
                  )

let add_equational_axioms context = 
  let axiom_pair =
    let vx = Why3.(Term.create_vsymbol (Ident.id_fresh "x")
                      (Ty.ty_app (Option.get context.msg_symb) [])) in
    let vy = Why3.(Term.create_vsymbol (Ident.id_fresh "y")
                      (Ty.ty_app (Option.get context.msg_symb) [])) in
    [(Symbols.fs_fst, vx); (Symbols.fs_snd, vy)]
    |> List.map (fun (proj, v) ->
        t_equ
          (t_app_infer
              (find_fn context proj)
              [t_app_infer
                (find_fn context Symbols.fs_pair)
                [t_var vx; t_var vy]])
          (t_var v))
    |> t_and_l
    |> t_forall_close [vx; vy] [] in

  let add_axiom
      (fname      : Symbols.fname)
      (def        : Symbols.OpData.abstract_def)
      (assoc_funs : Symbols.OpData.associated_fun)
    : (string * term) option
    =
    match def, assoc_funs with
    (* cases taken from Completion.init_erules *)
    | AEnc, [f1; f2] ->
      let dec, pk = (* from Completion.dec_pk *)
        match Symbols.OpData.get_abstract_data f1 context.table,
              Symbols.OpData.get_abstract_data f2 context.table with
        | (ADec     , _), (PublicKey, _) -> f1, f2
        | (PublicKey, _), (ADec     , _) -> f2, f1
        | _ -> assert false
      in
      (* we omit the check_zero_arities from Completion *)
      (* dec(enc(m, r, pk(k)), k) -> m *)
      let vars =
        List.map (fun str ->
            Why3.(Term.create_vsymbol (Ident.id_fresh str)
                    (Ty.ty_app 
                       (Option.get context.msg_symb) []
                    )
                 )
          ) ["m"; "r"; "k"]
      in
      let (vm, vr, vk) = as_seq3 vars in
      let term =
        t_equ (t_app_infer (find_fn context dec) 
                 [Why3.Term.t_tuple [t_app_infer (find_fn context fname) (* fname = enc *)
                    [Why3.Term.t_tuple [t_var vm; t_var vr;
                     t_app_infer (find_fn context pk)
                       [t_var vk]]];
                  t_var vk]])
          (t_var vm) |> t_forall_close vars []
      in
      Some ("axiom_aenc", term)

    | SEnc, [sdec] ->
      (* dec(enc(m, r, k), k) -> m *)
      let vars =
        List.map (fun str ->
            Why3.(Term.create_vsymbol (Ident.id_fresh str)
                    (Ty.ty_app 
                       (Option.get context.msg_symb) []
                    )
                 )
          ) ["m"; "r"; "k"]
      in
      let vm, vr, vk = as_seq3 vars in
      let term =
        t_equ (t_app_infer (find_fn context sdec)
                 [Why3.Term.t_tuple [t_app_infer (find_fn context fname)
                    [Why3.Term.t_tuple [t_var vm; t_var vr; t_var vk]];
                  t_var vk]])
          (t_var vm) |> t_forall_close vars []
      in
      Some ("axiom_senc", term)

    | CheckSign, [f1; f2] ->
      let msig, pk = (* from Completion.sig_pk *)
        match Symbols.OpData.get_abstract_data f1 context.table,
              Symbols.OpData.get_abstract_data f2 context.table with
        | (Sign     , _), (PublicKey, _) -> f1, f2
        | (PublicKey, _), (Sign     , _) -> f2, f1
        | _ -> assert false
      in
      (* mcheck(msig(m, k), pk(k)) -> true *)
      let vars =
        List.map (fun str ->
            Why3.(Term.create_vsymbol (Ident.id_fresh str)
                    (Ty.ty_app 
                       (Option.get context.msg_symb) 
                       []
                    )
                 )
          ) ["m"; "k"]
      in
      let vm, vk = as_seq2 vars in
      let term =
        Why3.Term.to_prop (t_app_infer (find_fn context fname)
                 [Why3.Term.t_tuple [t_var vm;t_app_infer (find_fn context msig)
                    [Why3.Term.t_tuple [t_var vm; t_var vk]];
                  t_app_infer (find_fn context pk)
                    [t_var vk]]])
        |> t_forall_close vars []
      in
      Some ("axiom_sig", term)

    | _ -> None
  in

  let equational_axioms =
    let open Symbols in
    Operator.fold (fun fname _ acc ->
        if OpData.is_abstract fname context.table then
          let def, assoc_funs = OpData.get_abstract_data fname context.table in
          Option.to_list (add_axiom fname def assoc_funs) @ acc
        else acc
      ) [("axiom_pair", axiom_pair)] context.table 
  in
  context.uc:=List.fold_left 
    (fun acc (id_ax, ax) ->
      Why3.Theory.add_decl_with_tuples acc 
      (Why3.Decl.create_prop_decl 
        Why3.Decl.Paxiom
        (Why3.Decl.create_prsymbol @@ id_fresh context id_ax)
        ax
      )
    ) 
    !(context.uc) (equational_axioms)
  
let add_macro_axioms context = 
  let macro_axioms = ref [] in
    SystemExpr.iter_descrs context.table (Option.get context.system) 
      (fun descr -> 
        let name_str = Symbols.to_string descr.name in
        (* TODO: quantified_vars is a recurring pattern *)
        let quantified_vars = ref (List.map (fun v ->
            let vsymb = create_vsymbol (id_fresh context (Vars.name v))
              (Why3.Ty.ty_app context.index_symb []) 
            in
            (* add to scope (shadow previous hash table binding) *)
            Hashtbl.add context.vars_tbl (Vars.hash v) (t_var vsymb);
            vsymb) descr.indices) in
        (* the call to ilist_to_wterm below already requires
          * that the index variables be in scope *)
        let ts = t_app_infer
          (fst(Hashtbl.find context.actions_tbl name_str)) 
          (ilist_to_wterm_ts context descr.indices) in 
        (* special handling for cond@ because it's a boolean
          * -> translated to formula, not term of type message unlike other macros
          * happens(A(i,...)) => (cond@A(i,...) <=> <the definition>) *)
        let ax_cond = t_implies (t_app_infer context.happens_symb [ts])
            (t_iff 
                (t_app_infer (Option.get context.macro_cond_symb) [ts])
                (msg_to_fmla context (snd descr.Action.condition))) in 
        macro_axioms := ("expand_cond_" ^ name_str,
                          t_forall_close !quantified_vars [] ax_cond) ::
                        !macro_axioms;
        
        Symbols.Macro.iter (fun mn _ -> 
            let mdef = Symbols.get_macro_data mn context.table in
            let m_str  = Symbols.to_string mn in
            let m_symb = Hashtbl.find context.macros_tbl m_str in
            let macro_wterm_eq indices msg =
              t_equ (t_app_infer m_symb (indices@[ts])) msg in
            let ax_option =
              begin match mdef with
              (* cond@ already handled above; exec@ defined in .why file *)
              | Symbols.Cond | Symbols.Exec -> None
              | Symbols.Output ->
                (* output@A(i1,...) = output *)
                Some (macro_wterm_eq
                        []
                        (msg_to_fmla context (snd descr.Action.output)))
              | Symbols.Global (arity, gty, _) -> begin 
                  (* for now, handle only the case where the indices of the macro
                      coincide with those of the action TODO *)
                  let m_idx = List.init arity (fun _ -> 
                    Vars.make_fresh Type.Index "i") in
                  let quantified_indices = List.map 
                    (fun v -> 
                      let vsymb = create_vsymbol (id_fresh context (Vars.name v))
                      (Why3.Ty.ty_app context.index_symb []) 
                      in
                      Hashtbl.add context.vars_tbl (Vars.hash v) (t_var vsymb);
                      vsymb
                    )m_idx in
                  let ax = match
                    Macros.get_definition_nocntxt 
                      (Option.get context.system) context.table
                      (Term.mk_symb mn gty) ~args:(Term.mk_vars m_idx)
                      descr.name (Term.mk_vars descr.indices)
                  with
                  | `Undef   -> None
                  | `Def msg ->
                    Some (t_forall_close quantified_indices [] (macro_wterm_eq
                            (List.map (index_var_to_wterm context) m_idx) 
                            (
                              (if gty=Type.Boolean 
                                then prop_to_bool else (fun x -> x)
                              )
                              (msg_to_fmla context msg)
                            )
                          ))
                in 
                List.iter 
                  (fun v -> Hashtbl.remove context.vars_tbl (Vars.hash v)) 
                  m_idx;
                ax
                end
              | Symbols.State (arity,sty, _) -> 
                (* TODO: could probably be treated by calling
                    Macros.get_definition_nocntxt, instead of copying its code
                    (but it would be annoying to handle fresh index variables)*)
                let quantified_indices =
                  List.init arity
                    (fun _ ->
                        Why3.(Term.create_vsymbol 
                        (Ident.id_fresh "i") context.index_ty)
                    )
                in
                let indices = List.map t_var quantified_indices in
                let expansion =
                  let same_as_pred =
                    t_app_infer m_symb
                      (indices @ [t_app_infer context.pred_symb [ts]]) in
                  try
                    let (_ns, ns_args, msg) =
                      List.find
                        (fun (ns,_,_) -> ns = mn)
                        descr.Action.updates
                    in
                    if descr.Action.name = Symbols.init_action then (
                      quantified_vars:=List.map (fun t -> 
                        match t with 
                          |Term.Var v -> 
                            let vsymb = create_vsymbol 
                              (id_fresh context (Vars.name v))
                              (Why3.Ty.ty_app context.index_symb []) 
                            in
                            Hashtbl.add context.vars_tbl 
                              (Vars.hash v) (t_var vsymb);
                            vsymb
                          |_ -> assert false 
                      )
                      ns_args
                    );
                    let expansion_ok = 
                      (if sty=Type.Boolean then prop_to_bool else (fun x -> x)) 
                      (msg_to_fmla context msg) 
                    in
                    if descr.Action.name = Symbols.init_action then
                      (List.iter (fun t -> 
                          match t with 
                            |Term.Var v -> 
                              Hashtbl.remove context.vars_tbl (Vars.hash v)
                            |_-> assert false
                        ) ns_args;
                      expansion_ok
                      )
                    else
                      (assert (List.inclusion (ns_args) (Term.mk_vars descr.indices));
                      t_if
                        (t_equ
                            (t_tuple indices)
                            (t_tuple (List.map (msg_to_fmla context) ns_args)))
                        expansion_ok
                        same_as_pred)
                  with Not_found -> same_as_pred in
                Some (t_forall_close quantified_indices []
                        (macro_wterm_eq indices expansion))
              | _ -> None (* input/frame, see earlier TODO *)
              end 
              (* TODO: do not do an exception catch-all *)
            in
            match ax_option with
            | None -> ()
            | Some ax ->
              (* forall i1 ... in : index. happens(A(i1,...)) => ... *)
              macro_axioms := ("expand_" ^ m_str ^ "_" ^ name_str,
                                t_forall_close !quantified_vars []
                                  (t_implies 
                                    (t_app_infer context.happens_symb [ts]) 
                                    ax
                                  )
                              )
                              :: !macro_axioms
          ) context.table; 
        (* cleanup scope  *)
        List.iter
          (fun v -> Hashtbl.remove context.vars_tbl (Vars.hash v)) descr.indices;
      );
  context.uc:=List.fold_left 
    (fun acc (id_ax, ax) ->
      Why3.Theory.add_decl_with_tuples acc 
      (Why3.Decl.create_prop_decl 
        Why3.Decl.Paxiom
        (Why3.Decl.create_prsymbol @@ id_fresh context id_ax)
        ax
      )
    )
    !(context.uc) (!macro_axioms)

let add_name_axioms context = 
  let name_inj_axioms =
    Symbols.Name.fold (fun n1 _ acc1 ->
      let def1 = Symbols.get_name_data n1 context.table in
      Symbols.Name.fold (fun n2 _ acc2 ->
        let def2 = Symbols.get_name_data n2 context.table in
        if (
          (def1.n_fty.fty_out = def2.n_fty.fty_out) && 
          (Symbols.TyInfo.check_bty_info context.table def1.n_fty.fty_out Large)
        ) then begin 
        let ar1,ar2 = calc_arity def1.n_fty.fty_args,
          calc_arity def2.n_fty.fty_args 
        in if n1 > n2 then acc2 else (* to avoid redundancy *)
        let l1,l2 = 
          vsymbol_list context "i" (List.init ar1 (fun _ -> context.index_ty)), 
          vsymbol_list context "j" (List.init ar2 (fun _ -> context.index_ty)) 
        in 
        let tl1,tl2 = List.map Why3.Term.t_var l1,List.map Why3.Term.t_var l2 in
          let ineq = t_neq
              (t_app_infer (Hashtbl.find context.names_tbl
                              (Symbols.to_string n1)) tl1)
              (t_app_infer (Hashtbl.find context.names_tbl
                              (Symbols.to_string n2)) tl2) in
          t_forall_close (l1@l2) []
            (if n1 = n2
              then t_implies (t_not (equal_lists context tl1 tl2)) ineq
              else ineq)
          :: acc2
        end
        else acc2 
      ) acc1 context.table) [] context.table 
  in
  context.uc:=List.fold_left 
    (fun acc (id_ax, ax) ->
      Why3.Theory.add_decl_with_tuples acc 
      (Why3.Decl.create_prop_decl 
        Why3.Decl.Paxiom
        (Why3.Decl.create_prsymbol @@ id_fresh context id_ax)
        ax
      )
    )
    !(context.uc) 
    (List.map (fun x -> ("axiom_distinct", x)) (name_inj_axioms))
  

let build_task ~timestamp_style ~pure table system
                evars hypotheses conclusion tm_theory = 

  let context = context_init ~timestamp_style ~pure tm_theory evars table system
  in 
  if system<>None then (
      add_actions context; 
      add_timestamp_axioms context
  );
  add_var context;
  if not context.pure then (
    add_functions context;
    add_macros context;
    add_names context;
    add_equational_axioms context;
    if system<>None then add_macro_axioms context;
    add_name_axioms context
  );
    

(*Converts hypotheses with 'and' at top level to two hypotheses*)
  let rec convert_hypotheses hypotheses= match hypotheses with 
    |[]->[]
    |t::q -> match Term.destr_and t with
      |Some (t1, t2) -> t1::(convert_hypotheses (t2::q))
      |None -> t::(convert_hypotheses q)
  in 
  let decl = Why3.Decl.create_prop_decl 
    Why3.Decl.Pgoal
    (Why3.Decl.create_prsymbol @@ id_fresh context "GOAL")
    (Why3.Term.t_not
      (Why3.Term.t_and
        (Why3.Term.t_and_l
          (List.filter_map
            (fun h ->
              try Some (msg_to_fmla context h) with InternalError -> None)
            (convert_hypotheses hypotheses)))
        (Why3.Term.t_not 
          (try msg_to_fmla context conclusion with 
            InternalError -> Why3.Term.t_false))))
  in
  let uc : Why3.Theory.theory_uc =
    let module Mid = Why3.Ident.Mid in
    let module Sid = Why3.Ident.Sid in
    let used_syms : Sid.t = Why3.Decl.get_used_syms_decl decl in 
    let unknown_tsyms = Mid.set_diff used_syms !(context.uc).uc_known in
    Sid.fold
      (fun symb uc ->
         match Why3.Ty.is_ts_tuple_id symb with
         | Some n -> Why3.Theory.(use_export uc (tuple_theory n))
         | None ->
           assert (Why3.Term.is_fs_tuple_id symb <> None);
           uc)
      unknown_tsyms
      !(context.uc)
  in
  let task = Why3.Task.use_export None (Why3.Theory.close_theory uc) in
  Why3.Task.add_decl task decl


let unique_id =
  let id = ref 0 in
  fun () -> incr id ; !id

let is_valid
    ~timestamp_style ~pure ~slow ~provers
    table system evars hypotheses conclusion
  =
  let theory = match load_theory ~timestamp_style ~pure env with
    | Some theory -> theory
    | None -> Format.printf "Load theory failed@."; raise InternalError
  in
  let task = build_task
    ~timestamp_style ~pure
    table system
    evars hypotheses conclusion
    theory
  in
  begin match Sys.getenv_opt "SMT_VERBOSE" with
    | None -> ()
    | Some filename ->
      let oc = open_out_gen [Open_append;Open_creat] 0o644 filename in
      let ppf = Format.formatter_of_out_channel oc in
      Format.fprintf ppf "Id %d@." (unique_id ());
      Format.fprintf ppf "%a@." Why3.Pretty.print_task task;
      close_out oc
  end;
  if smt_debug then
    Format.printf "%a@." Why3.Pretty.print_task task;
  run_all_async ~slow ~provers table task

(* Tactic registration *)

let sequent_is_valid ~timestamp_style ~slow ~pure ~provers (s:TraceSequent.t) =
  let env = TraceSequent.env s in
  let table = env.table in
  let system = match SystemExpr.to_fset env.system.set with 
    | exception SystemExpr.(Error (_,Expected_fset)) -> None 
    | fsys -> Some fsys 
  in
  let evars = Vars.to_vars_list env.vars in
  let hypotheses =
    Hint.get_smt_db table @
    List.filter_map
      (function
         | _, Hyps.LHyp (Equiv.Local h) -> Some h
         | _, Hyps.LHyp (Equiv.(Global Atom (Reach f))) -> Some f
         | _ -> None)
      (LowTraceSequent.Hyps.to_list s)
  in
  let conclusion = LowTraceSequent.conclusion s in
  try is_valid ~timestamp_style ~slow ~pure ~provers
    table system evars hypotheses conclusion
  with 
    |e -> raise e

type parameters = {
  timestamp_style : timestamp_style;
  slow : bool;
  pure : bool;
  provers : (string*string) list
}

let default_parameters = {
  timestamp_style = Nat;
  slow = false;
  pure = false ;
  provers = ["CVC5",""]
}

let parse_prover_arg prover_alt =
  let add_dash s = if s = "AltErgo" then "Alt-Ergo" else s in
  match String.split_on_char '_' prover_alt with
    | [p;alt] -> add_dash p, alt
    | [p] -> add_dash p, ""
    | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))

let parse_arg parameters = function

  (* Translation style for timestamps *)
  | TacticsArgs.NList ({Location.pl_desc="style"},
                       [{Location.pl_desc="abstract"}]) ->
    { parameters with timestamp_style = Abstract }
  | TacticsArgs.NList ({Location.pl_desc="style"},
                       [{Location.pl_desc="nat"}]) ->
    { parameters with timestamp_style = Nat }
  | TacticsArgs.NList ({Location.pl_desc="style"},
                       [{Location.pl_desc="abstract_eq"}]) ->
    { parameters with timestamp_style = Abstract_eq }

  (* Provers *)
  | TacticsArgs.NList ({Location.pl_desc="prover"},l)
  | TacticsArgs.NList ({Location.pl_desc="provers"},l) ->
    let process_prover provers {Location.pl_desc=prover_alt} =
      parse_prover_arg prover_alt :: provers
    in
    { parameters with provers = List.fold_left process_prover [] l }

  (* Other flags *)
  | TacticsArgs.NArg {Location.pl_desc="slow"}
  | TacticsArgs.NList ({Location.pl_desc="slow"},
                       [{Location.pl_desc="true"}]) ->
    { parameters with slow=true }
  | TacticsArgs.NList ({Location.pl_desc="slow"},
                       [{Location.pl_desc="false"}]) ->
    { parameters with slow=false }
  | TacticsArgs.NArg {Location.pl_desc="pure"}
  | TacticsArgs.NList ({Location.pl_desc="pure"},
                       [{Location.pl_desc="true"}]) ->
    { parameters with pure=true }
  | TacticsArgs.NList ({Location.pl_desc="pure"},
                       [{Location.pl_desc="false"}]) ->
    { parameters with pure=false }
  | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))

let parse_args args =
  List.fold_left parse_arg default_parameters args

let () =
  ProverTactics.register_general "smt" ~pq_sound:true
    (fun args s sk fk ->
       let args = match args with
         | [Named_args args] -> args
         | _ -> assert false
       in
       let s = match s with
         | Goal.Global _ -> Tactics.(hard_failure (Failure "SMT not available"))
         | Goal.Local s -> s
       in
       let {timestamp_style;slow;pure;provers} = parse_args args in
       if
         sequent_is_valid
          ~timestamp_style ~slow ~pure
          ~provers
          s
       then
         sk [] fk
       else
         fk (None, Tactics.Failure "SMT cannot prove sequent"))

let () =
  let provers =
    match Sys.getenv_opt "SMT_PROVERS" with
    | None -> ["CVC5",""]
    | Some s -> List.map parse_prover_arg (String.split_on_char ':' s)
  in
  let timestamp_style = match Sys.getenv_opt "SMT_STYLE" with
    | Some "AbsNoEq" -> Abstract
    | Some "Abs" -> Abstract_eq
    | Some "Nat" | Some "" | None -> Nat
    | _ ->
      Format.eprintf "Unknown timestamp style!@.";
      Format.eprintf "If set and non-empty, \
                      SMT_STYLE must be Nat, Abs, or AbsNoEq.@.";
      exit 1
  in
  let benchmarks =
    match Sys.getenv_opt "SMT_BENCHMARKS" with
    | None -> []
    | Some s -> String.split_on_char ':' s
  in
  let bench_name prover alt =
    let alt = if alt = "" then alt else "_" ^ alt in
    Format.sprintf "SMT_%s%s" prover alt
  in
  if List.mem "constr" benchmarks then
    List.iter
      (fun (prover,alt) ->
         TraceSequent.register_query_alternative
           (bench_name prover alt)
           (fun ~precise:_ s q ->
              let s =
                match q with
                | None -> s
                | Some q ->
                  let conclusion =
                    Term.mk_ands (List.map Term.Lit.lit_to_form q) in
                  TraceSequent.set_conclusion conclusion s
              in
              sequent_is_valid
                ~timestamp_style
                ~slow:false
                ~pure:false
                ~provers:[prover,alt]
                s))
      provers;
  if List.mem "autosimpl" benchmarks then
    List.iter
      (fun (prover,alt) ->
         TraceTactics.AutoSimplBenchmark.register_alternative
           (bench_name prover alt)
           (fun s ->
              sequent_is_valid
                ~timestamp_style
                ~slow:false
                ~pure:false
                ~provers:[prover,alt]
                s,
              None))
      provers;
  if List.mem "auto" benchmarks then
    List.iter
      (fun (prover,alt) ->
         TraceTactics.AutoBenchmark.register_alternative
           (bench_name prover alt)
           (fun (_,s) ->
              sequent_is_valid
                ~timestamp_style
                ~slow:false
                ~pure:false
                ~provers:[prover,alt]
                s))
      provers
