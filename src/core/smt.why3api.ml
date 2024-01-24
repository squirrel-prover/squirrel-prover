open Utils

(** Style for translating timestamps. *)
type timestamp_style =
  | Abstract     (** Abstract with specific ~~ for comparison. *)
  | Abstract_eq  (** Abstract with builtin equality for comparison. *)
  | Nat          (** Natural numbers. *)

let start_timer () =
  Format.printf "<< TOP CHRONO >>@.";
  let t0 = Unix.gettimeofday () in
  fun () ->
    Format.printf "<< ELAPSED %.3fs >>@." (Unix.gettimeofday () -. t0)
    
let config = Why3.Whyconf.init_config None

let main = Why3.Whyconf.get_main config

let provers = Why3.Whyconf.get_provers config

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
                    |Abstract -> "__abs" | Abstract_eq -> "_abs_eq" | _ ->"") in
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
    Some (Why3.Driver.prove_task
      ~config:main
      ~command:config_prover.command
      ~limit:
        { Why3.Call_provers.empty_limit with limit_time = float_of_int limit }
      driver
      task)
  with e ->
    Format.printf
      "SMT: %s driver failed to load: %a@.\n"
      prover.Why3.Whyconf.prover_name Why3.Exn_printer.exn_printer e;
      None

let run_one ~slow prover table task =
  let timer = start_timer () in
  try
    let prover,config_prover =
    Why3.Whyconf.(Mprover.max_binding
                    (filter_provers config
                    (parse_filter_prover prover)))
    in
    let call =
      if slow 
      then create_call ~limit_opt:60 prover table config_prover task 
      else create_call prover table config_prover task
    in 
    match call with 
      |Some call -> let r = Why3.Call_provers.wait_on_call call in
      timer ();Some r
      |None -> None
  with Not_found -> Format.printf "SMT: %s prover not found\n" prover; None
  
let run_all_async ~slow table task =
  Why3.Prove_client.set_max_running_provers 4;
  let timer = start_timer () in
  let calls :
    (Why3.Whyconf.prover*Why3.Call_provers.prover_call)
    Why3.Whyconf.Mprover.t
  =
    Why3.Whyconf.Mprover.mapi_filter
      (fun prover config_prover -> 
        let call = if slow 
          then create_call ~limit_opt:60 prover table config_prover task
          else create_call prover table config_prover task
        in match call with 
          |Some call -> Some (prover,call)
          |None -> None
      )
      provers
  in
  (* Number of calls for which we still need a result. *)
  let n = ref @@ Why3.Whyconf.Mprover.cardinal calls in
  Format.eprintf "Waiting for new results...@.";
  let res = ref false in
  while !n>0 do
    let l = Why3.Call_provers.get_new_results ~blocking:true in
    timer ();
    res := List.fold_left
      (fun acc (prover_call,prover_update) ->
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
            (r.pr_answer = Why3.Call_provers.Valid) || acc
        | _ ->
           Format.eprintf "Other@.";acc)
      false l || !res;
  done;
  timer ();!res
  
(** Context for SMT translation, providing information on:
    - the Squirrel formulas being translated (e.g. table, system expression);
    - the SMT formulas (declared symbols and variables);
    - the translation mode. *)
type context = { 
  table : Symbols.table;
  system : SystemExpr.fset;

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

exception Unsupported of Term.term
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
let index_to_wterm context i = Hashtbl.find context.vars_tbl (Vars.hash i) 
let ilist_to_wterm_ts context l = List.map (index_to_wterm context) l 

let rec timestamp_to_wterm context = function
  | Term.App (Fun (fs, _), [ts]) when fs = Term.f_pred ->
    t_app_infer context.pred_symb [timestamp_to_wterm context ts]
  | Term.Action (a, indices) ->
    (match indices with 
      |[Tuple ind_list] -> 
        t_app_infer (fst(Hashtbl.find context.actions_tbl (Symbols.to_string a))) 
        (ilist_to_wterm_ts context (List.map (oget -| Term.destr_var) ind_list))

      |_ -> 
        t_app_infer (fst(Hashtbl.find context.actions_tbl (Symbols.to_string a)))
        (ilist_to_wterm_ts context (List.map (oget -| Term.destr_var) indices))
      
    )
    
  | Var v -> Hashtbl.find context.vars_tbl (Vars.hash v)
  | Diff _ -> 
    failwith "diff of timestamps to why3 term not implemented"
  | _ -> assert false

let rec atom_to_fmla context : Term.Lit.xatom -> Why3.Term.term = fun atom ->
  let handle_eq_atom rec_call = match atom with
    | Comp (`Eq, x, y)  -> t_equ (rec_call x) (rec_call y) 
    | Comp (`Neq, x, y) -> t_neq (rec_call x) (rec_call y)
    |Atom x -> if context.pure then assert false 
      else begin let t = rec_call x in 
        match (t_type t) with 
          |ty when ty=(Option.get context.msg_ty) -> assert false
          | _ -> Why3.Term.to_prop t
      end
    | _ -> assert false
  in
  match Term.Lit.ty_xatom atom with
  | Type.Timestamp -> begin match atom with
      | Comp (comp,ts1,ts2) ->
        let listargs = List.map (timestamp_to_wterm context) [ts1;ts2] in
        let t1,t2 = List.nth listargs 0, List.nth listargs 1 in 
        begin match comp with
          | `Eq  -> ts_equ context t1 t2 
          | `Neq -> t_not (ts_equ context t1 t2 )
          | `Leq -> t_app_infer context.leq_symb listargs
          | `Geq -> t_app_infer context.leq_symb (List.rev listargs)
          | `Lt  -> t_and (t_app_infer context.leq_symb listargs)
                      (t_not @@ ts_equ context t1 t2 )
          | `Gt  -> let listargs = List.rev listargs in
            t_and (t_app_infer context.leq_symb listargs)
              (t_not @@ ts_equ context t1 t2 )
        end
      | Happens ts -> Why3.Term.t_app_infer 
        context.happens_symb [timestamp_to_wterm context ts]
      | Atom _ -> assert false (* cannot happen *)
    end
  | Type.Index -> handle_eq_atom (function
      | Term.Var i -> index_to_wterm context i
      | _          -> assert false)
  | _          -> if context.pure 
    then raise (Unsupported (Term.Lit.xatom_to_form atom)) 
    else handle_eq_atom (msg_to_wterm context)
and _lit_to_fmla context : Term.Lit.literal -> Why3.Term.term = function
  | (`Pos, x) ->        atom_to_fmla context x
  | (`Neg, x) -> t_not (atom_to_fmla context x)
and find_fn context f = Hashtbl.find context.functions_tbl (Symbols.to_string f)

and msg_to_wterm context : Term.term -> Why3.Term.term = fun c ->
  let open Term in
  let open Why3.Term in
  match c with (* cases taken from Completion.cterm_of_term *)
  | Fun (f,_) -> t_app_infer (find_fn context f) []

  | App (Fun (f,_),terms) ->
    begin match terms with
      | [t1; t2] when f = Symbols.fs_xor ->
        t_app_infer 
        (Option.get context.xor_symb)
          [msg_to_wterm context t1; 
          msg_to_wterm context t2]
      | [cond; t1; t2] when f = Symbols.fs_ite -> 
        (* Special case for if-then-else:
         * the benefit is not just to use the "native" why3 conditional
         * but also to translate the condition into a formula
         * (this avoids the need for a conversion from atoms to why3 terms
         * of type message). *)
        t_if (msg_to_fmla context cond) 
          (msg_to_wterm context t1) 
          (msg_to_wterm context t2)
      | _ -> t_app_infer 
        (find_fn context f) 
        (List.map (msg_to_wterm context) terms)
    end

  | Macro (ms,l,ts) -> 
    (match l with 
      |[Tuple l_list] ->t_app_infer
        (Hashtbl.find context.macros_tbl (Symbols.to_string ms.s_symb))
        (List.map (index_to_wterm context -| oget -| Term.destr_var) l_list @
        [timestamp_to_wterm context ts])
      |_ ->t_app_infer
        (Hashtbl.find context.macros_tbl (Symbols.to_string ms.s_symb))
        (List.map (index_to_wterm context -| oget -| Term.destr_var) l @
        [timestamp_to_wterm context ts])
    )
    
  | Name (ns,args) ->
      (match args with 
      |[Tuple args_list] -> t_app_infer
        (Hashtbl.find context.names_tbl (Symbols.to_string ns.s_symb))
        (ilist_to_wterm_ts context (List.map (oget -| Term.destr_var) args_list))
      |_ -> t_app_infer
      (Hashtbl.find context.names_tbl (Symbols.to_string ns.s_symb))
      (ilist_to_wterm_ts context (List.map (oget -| Term.destr_var) args))
    )

  | Diff _ -> failwith "diff of timestamps to why3 term not implemented"

  | Var v -> 
    begin try Hashtbl.find context.vars_tbl (Vars.hash v) with
      | Not_found ->
        raise InternalError
    end

  | Tuple l -> t_tuple (List.map (msg_to_wterm context) l)
  | _ -> assert false

and msg_to_fmla context : Term.term -> Why3.Term.term = fun fmla ->
  match fmla,context.pure with 
    | Term.App (Fun (symb,_),_),_ when symb = Term.f_false -> t_false
    | Term.App (Fun (symb,_),_),_ when symb = Term.f_true -> t_true
    | Term.App (Fun (symb,_),[f]),_ when symb = Term.f_not ->
      t_not (msg_to_fmla context f)
    | Term.App (Fun (symb,_),[f1;f2]),_ when symb = Term.f_and ->
      t_and (msg_to_fmla context f1) (msg_to_fmla context f2)
    | Term.App (Fun (symb,_),[f1;f2]),_ when symb = Term.f_or ->
      t_or (msg_to_fmla context f1) (msg_to_fmla context f2)
    | Term.App (Fun (symb,_),[f1;f2]),_ when symb = Term.f_impl ->
      t_implies (msg_to_fmla context f1) (msg_to_fmla context f2)  
    | Term.Quant (ForAll, vs, f),_ -> msg_to_fmla_q context t_forall_close vs f
    | Term.Quant (Exists, vs, f),_ -> msg_to_fmla_q context t_exists_close vs f
    | Macro (ms,[],ts),false when ms.s_symb = Symbols.cond ->
      t_app_infer 
        (Option.get context.macro_cond_symb)
        [timestamp_to_wterm context ts]
    | Macro (ms,[],ts),false when ms.s_symb = Symbols.exec ->
      t_app_infer 
        (Option.get context.macro_exec_symb) 
        [timestamp_to_wterm context ts]
    | _ -> match Term.Lit.form_to_xatom fmla with 
      | Some at -> atom_to_fmla context at
      | None -> assert false
    
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
    assert (not (Hashtbl.mem tbl (Vars.hash v)));
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
let add_actions context = SystemExpr.iter_descrs context.table context.system 
(fun descr -> 
  if descr.name <> Symbols.init_action then
    let str = Symbols.to_string descr.name in
    let symb_act = Why3.Term.create_fsymbol
        (id_fresh context str)
        (List.init (List.length descr.indices) (fun _ -> context.index_ty))
        context.ts_ty
      in
      Hashtbl.add context.actions_tbl str (symb_act,List.length descr.indices)
);
context.uc:=Hashtbl.fold 
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
  Symbols.Function.iter (fun fname (ftype, _) _ ->
    let str = Symbols.to_string fname in
    (* special treatment of xor for two reasons:
     *   - id_fresh doesn't avoid the "xor" why3 keyword (why3 api bug?)
     *   - allows us to declare the equations for xor in the .why file *)
    if (
      fname <> Symbols.fs_xor && fname <> Symbols.fs_pair && 
      fname <> Symbols.fs_fst && fname <> Symbols.fs_snd && 
      fname <>Symbols.fs_att && fname<>Symbols.fs_of_bool && 
      fname<>Symbols.fs_empty && fname<>Symbols.fs_pred && 
      fname<>Symbols.fs_happens
    ) then
    (* TODO can't declare polymorphic symbols... yet? *)
    if ftype.Type.fty_vars <> [] then
      Format.printf "Cannot declare %s : %a@." str Type.pp_ftype ftype
    else begin 
      let symb =
        Why3.Term.create_fsymbol
          (id_fresh context str)
          (List.map (convert_type context) ftype.fty_args)
          (convert_type context ftype.fty_out)
      in
      Hashtbl.add context.functions_tbl str (symb)
    end;
    ) context.table;
    context.uc:= Hashtbl.fold 
    (fun _ (symb) uc ->
       Why3.Theory.add_decl_with_tuples uc (Why3.Decl.create_param_decl symb)
    ) context.functions_tbl !(context.uc);
    List.iter (fun (fname,symb) ->
      Hashtbl.add context.functions_tbl 
        (Symbols.to_string fname) 
        (symb)
      ) 
      [(Symbols.fs_pair,(Option.get context.pair_symb));
        (Symbols.fs_fst,(Option.get context.fst_symb));
        (Symbols.fs_snd,(Option.get context.snd_symb));
        (Symbols.fs_att,(Option.get context.att_symb));
        (Symbols.fs_of_bool,(Option.get context.of_bool_symb));
        (Symbols.fs_empty,(Option.get context.empty_symb));
      ]


let add_macros context = 
  Symbols.Macro.iter (fun mn def _ ->
    let str = Symbols.to_string mn in
    let indices = match def with
      | Input | Output | Cond | Exec | Frame -> 0
      | State (i,Type.Message) -> i
      | Global (i,Type.Message) -> i
      | _ ->
        Format.printf "smt: unsupported macro def@.";
        raise InternalError
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
        |State(_,t) | Global(_,t) -> convert_type context t 
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

let add_names context = 
  Symbols.Name.iter (fun name def _ ->
    let str = Symbols.to_string name in
    let arity = calc_arity def.n_fty.fty_args in 
    let symb =
      Why3.Term.create_fsymbol
        (id_fresh context str)
        (List.init arity (fun _ -> context.index_ty)) 
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
    ) context.table context.system acc) context.table context.system [] 
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
  
  let equational_axioms =
    let open Symbols in
    Function.fold (fun fname def data acc ->
        match (snd def), data with
        (* cases taken from Completion.init_erules *)
        | AEnc, AssociatedFunctions [f1; f2] ->
          let dec, pk = (* from Completion.dec_pk *)
            match Function.get_def f1 context.table,
                  Function.get_def f2 context.table with
            | (_, ADec), (_, PublicKey) -> f1, f2
            | (_, PublicKey), (_, ADec) -> f2, f1
            | _ -> assert false
          in
          (* we omit the check_zero_arities from Completion *)
          (* dec(enc(m, r, pk(k)), k) -> m *)
          begin match List.map (fun str ->
              Why3.(Term.create_vsymbol (Ident.id_fresh str)
                      (Ty.ty_app 
                        (Option.get context.msg_symb) []
                      )
                    )
          ) ["m"; "r"; "k"] with
            | [vm; vr; vk] as vars ->
              ("axiom_aenc",
                t_equ (t_app_infer (find_fn context dec) 
                        [t_app_infer (find_fn context fname) (* fname = enc *)
                            [t_var vm; t_var vr;
                            t_app_infer (find_fn context pk)
                              [t_var vk]];
                          t_var vk])
                  (t_var vm) |> t_forall_close vars [])
              :: acc
            | _ -> assert false
          end
        | SEnc, AssociatedFunctions [sdec] ->
          (* dec(enc(m, r, k), k) -> m *)
          begin match List.map (fun str ->
              Why3.(Term.create_vsymbol (Ident.id_fresh str)
                      (Ty.ty_app 
                        (Option.get context.msg_symb) []
                      )
                    )
          ) ["m"; "r"; "k"] with
            | [vm; vr; vk] as vars ->
              ("axiom_senc",
                t_equ (t_app_infer (find_fn context sdec)
                        [t_app_infer (find_fn context fname)
                            [t_var vm; t_var vr; t_var vk];
                          t_var vk])
                  (t_var vm) |> t_forall_close vars [])
              :: acc
            | _ -> assert false
          end
        | CheckSign, AssociatedFunctions [f1; f2] ->
          let msig, pk = (* from Completion.sig_pk *)
            match Function.get_def f1 context.table,
                  Function.get_def f2 context.table with
            | (_, Sign), (_, PublicKey) -> f1, f2
            | (_, PublicKey), (_, Sign) -> f2, f1
            | _ -> assert false
          in
          (* mcheck(msig(m, k), pk(k)) -> true *)
          begin match List.map (fun str ->
              Why3.(Term.create_vsymbol (Ident.id_fresh str)
                      (Ty.ty_app 
                        (Option.get context.msg_symb) 
                        []
                      )
                    )
          ) ["m"; "k"] with
            | [vm; vk] as vars ->
              ("axiom_sig",
                t_equ (t_app_infer (find_fn context fname)
                        [t_app_infer (find_fn context msig)
                            [t_var vm; t_var vk];
                          t_app_infer (find_fn context pk)
                            [t_var vk]])
                  (t_app_infer (find_fn context Symbols.fs_true) [])
                |> t_forall_close vars [])
              :: acc
            | _ -> assert false
          end
        | _ -> acc
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
    SystemExpr.iter_descrs context.table context.system (fun descr ->
        let name_str = Symbols.to_string descr.name in
        (* TODO: quantified_vars is a recurring pattern *)
        let quantified_vars = List.map (fun v ->
            let vsymb = create_vsymbol (id_fresh context (Vars.name v))
              (Why3.Ty.ty_app context.index_symb []) 
            in
            (* add to scope (shadow previous hash table binding) *)
            Hashtbl.add context.vars_tbl (Vars.hash v) (t_var vsymb);
            vsymb) descr.indices in
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
                          t_forall_close quantified_vars [] ax_cond) ::
                        !macro_axioms;
        Symbols.Macro.iter (fun mn mdef _mdata ->
            let m_str  = Symbols.to_string mn in
            let m_symb = Hashtbl.find context.macros_tbl m_str in
            let macro_wterm_eq indices msg =
              t_equ (t_app_infer m_symb (indices@[ts])) msg in
            let ax_option = try begin match mdef with
              (* cond@ already handled above; exec@ defined in .why file *)
              | Symbols.Cond | Symbols.Exec -> None
              | Symbols.Output ->
                (* output@A(i1,...) = output *)
                Some (macro_wterm_eq
                        []
                        (msg_to_wterm context (snd descr.Action.output)))
              | Symbols.Global (arity, gty) -> begin
                  (* for now, handle only the case where the indices of the macro
                      coincide with those of the action TODO *)
                  let m_idx = Utils.List.take arity descr.indices in
                  match
                    Macros.get_definition_nocntxt context.system context.table
                      (Term.mk_symb mn gty) ~args:(Term.mk_vars m_idx)
                      descr.name (Term.mk_vars descr.indices)
                  with
                  | `Undef   -> None
                  | `Def msg ->
                    Some (macro_wterm_eq
                            (List.map (index_to_wterm context) m_idx)
                            (msg_to_wterm context msg))
                end
              | Symbols.State (arity,_) ->
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
                    let expansion_ok = msg_to_wterm context msg in
                    if descr.Action.name = Symbols.init_action then
                      expansion_ok
                    else
                      t_if
                        (t_equ
                            (t_tuple indices)
                            (t_tuple (List.map (msg_to_wterm context) ns_args)))
                        expansion_ok
                        same_as_pred
                  with Not_found -> same_as_pred in
                Some (t_forall_close quantified_indices []
                        (macro_wterm_eq indices expansion))
              | _ -> None (* input/frame, see earlier TODO *)
            end with Unsupported _ -> None
            in
            match ax_option with
            | None -> ()
            | Some ax ->
              (* forall i1 ... in : index. happens(A(i1,...)) => ... *)
              macro_axioms := ("expand_" ^ m_str ^ "_" ^ name_str,
                                t_forall_close quantified_vars []
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
  let name_inj_axioms = Symbols.Name.fold (fun n1 def1 _ acc1 ->
    Symbols.Name.fold (fun n2 def2 _ acc2 ->
        if (
          (def1.n_fty.fty_out = def2.n_fty.fty_out) && 
          (Symbols.TyInfo.check_bty_info context.table def1.n_fty.fty_out Large)
        ) then begin 
        let ar1,ar2 = calc_arity def1.n_fty.fty_args,
          calc_arity def2.n_fty.fty_args 
        in
        if n1 > n2 then acc2 else (* to avoid redundancy *)
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
  add_actions context; 
  add_var context;
  add_timestamp_axioms context;
  if not context.pure then (
    add_functions context;
    add_macros context;
    add_names context;
    add_equational_axioms context;
    add_macro_axioms context;
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
              try Some (msg_to_fmla context h) with Unsupported _ -> None)
            (convert_hypotheses hypotheses)))
        (Why3.Term.t_not 
          (try msg_to_fmla context conclusion with 
            Unsupported _ -> Why3.Term.t_false))))
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


       (* }}} *)

let is_valid
    ~timestamp_style ~pure ~slow ~prover
    table system evars hypotheses conclusion
  =
  try
    let theory = match load_theory ~timestamp_style ~pure env with 
      |Some theory -> theory
      |None -> raise InternalError
    in  
    let task = build_task 
      ~timestamp_style ~pure 
      table system 
      evars hypotheses conclusion 
      theory 
    in Format.printf "Task is:@;%a@." Why3.Pretty.print_task task;
    if prover="" then run_all_async ~slow table task else 
    begin match 
      run_one ~slow prover table task 
    with  
    | None ->
      Format.printf "Answer: None.@." ;
      false
    | Some Why3.Call_provers.{pr_answer} ->
      Format.printf "Answer: %a@."
        Why3.Call_provers.print_prover_answer
        pr_answer ;
      pr_answer = Why3.Call_provers.Valid
    end
  with
    | Unsupported t ->
      Format.printf "smt: cannot translate term %a@." Term.pp t;
      false
    | InternalError ->
      Format.printf "smt: internal error@.";
      false
      
(* Tactic registration *)

let sequent_is_valid ~prover ~timestamp_style (s:TraceSequent.t) =
  let env = TraceSequent.env s in
  let table = env.table in
  let system = SystemExpr.to_fset env.system.set in
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
  is_valid ~timestamp_style ~slow:false ~pure:false ~prover
    table system evars hypotheses conclusion

type parameters = {
  timestamp_style : timestamp_style;
  provers : string list
}

let default_parameters = {
  timestamp_style = Nat;
  provers = []
}
let parse_arg parameters = function
  | TacticsArgs.NList ({Location.pl_desc="style"},[{Location.pl_desc="abstract_ax"}]) ->
    { parameters with timestamp_style = Abstract }
  | TacticsArgs.NList ({Location.pl_desc="style"},[{Location.pl_desc="nat"}]) ->
    { parameters with timestamp_style = Nat }
  | TacticsArgs.NList ({Location.pl_desc="style"},[{Location.pl_desc="abstract_eq"}]) ->
    { parameters with timestamp_style = Abstract_eq }
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
       let parameters = parse_args args in
       let is_valid =
         sequent_is_valid
           ~prover:(match parameters.provers with [] -> "CVC4" | hd::_ -> hd)
           ~timestamp_style:parameters.timestamp_style
           s
       in
       if is_valid then sk [] fk else fk (None, Tactics.Failure "SMT cannot prove sequent"))

let () =
  if Sys.getenv_opt "BENCHMARK_SMT" <> None then
    (* TODO benchmark several provers and styles, runnning each one separately,
       and restrict to reasoning on pure formulas *)
    TraceSequent.Benchmark.register_query_alternative
      "Smt"
      (fun ~precise:_ s q ->
        let s =
          match q with
          | None -> s
          | Some q ->
            let conclusion = Term.mk_ands (List.map Term.Lit.lit_to_form q) in
            TraceSequent.set_conclusion conclusion s
        in
        sequent_is_valid
          ~prover:"CVC4"
          ~timestamp_style:Nat
          s)