open Utils

module SE = SystemExpr

(*------------------------------------------------------------------*)
(* use [_] instead of [.] in path when building Why3 names. *)
let path_to_string p = Symbols.path_to_string ~sep:"_" p

(*------------------------------------------------------------------*)
let smt_debug = Sys.getenv_opt "SMT_DEBUG" <> None

let start_timer () =
  let t0 = Unix.gettimeofday () in
  fun () -> Unix.gettimeofday () -. t0

(* If we are running in JS, we disable smt. *)
let disable_smt =
  let exec_dir = Filename.dirname Sys.executable_name in
  exec_dir = "."

let config =
  if disable_smt then
    Why3.Whyconf.read_config (Some "")
  else
    Why3.Whyconf.init_config None

let main = Why3.Whyconf.get_main config

let why3_provers = Why3.Whyconf.get_provers config

let env =
  let exec_dir = Filename.dirname Sys.executable_name in
  Why3.Env.create_env
    (Filename.(concat exec_dir "theories") ::
        Why3.Whyconf.(loadpath (get_main config)))

let load_theory env =
  try
    let theory = "trace_model"
    in
    Some (Why3.Env.read_theory env [theory] (String.capitalize_ascii theory))
  with
  | Why3.Env.LibraryConflict _ | Why3.Env.LibraryNotFound _
  | Why3.Env.AmbiguousPath   _ | Why3.Env.TheoryNotFound  _ ->
    Format.printf "SMT: error while loading SMT theory file\n"; None

let create_call limit_time steps prover cmd_flag config_prover task :
  Why3.Call_provers.prover_call option =
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
    if smt_debug then begin
      Why3.Debug.set_flag (Why3.Debug.lookup_flag "call_prover");
      let fname = Filename.temp_file "why3_task_pretask" ".txt" in
      let oc = open_out_gen [Open_append;Open_creat] 0o644 fname in
      let ppf = Format.formatter_of_out_channel oc in
      Format.fprintf ppf "Task: @.@.%a@." Why3.Pretty.print_task task;
      Format.fprintf ppf "Prepared task: @.@.%a@."
        Why3.Pretty.print_task (Why3.Driver.prepare_task driver task);
      close_out oc
    end;
    let limits, cmd = match steps with
      | None ->
        { Why3.Call_provers.empty_limits
          with limit_time = float_of_int limit_time },
        config_prover.command
      | Some s ->
        { Why3.Call_provers.empty_limits with limit_steps = s },
        Option.get config_prover.command_steps
    in
    Some
      (Why3.Driver.prove_task
          ~config:main
          ~command:(cmd^" "^cmd_flag)
          ~limits
          driver
          task)
  with e ->
    Format.printf
      "SMT: %s driver failed to load: %a@.\n"
      prover.Why3.Whyconf.prover_name Why3.Exn_printer.exn_printer e;
    None

let run_all_async ~timeout ~steps ~provers ~cmd_flag task =
  Why3.Prove_client.set_max_running_provers 4;
  let timer = start_timer () in
  let calls :
    (Why3.Whyconf.prover*Why3.Call_provers.prover_call)
      Why3.Whyconf.Mprover.t
    =
    Why3.Whyconf.Mprover.mapi_filter
      (fun p config_prover ->
          if List.mem Why3.Whyconf.(p.prover_name,p.prover_altern) provers then
            let call = create_call timeout steps p cmd_flag config_prover task in
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
  while !n>0 do
    if smt_debug then
      Format.eprintf "Waiting for %d interrupted calls...@." !n;
    let results = Why3.Call_provers.get_new_results ~blocking:true in
    if smt_debug then
      Format.printf
        "%d result(s) obtained after %.2fs.@."
        (List.length results)
        (timer ());
    n := !n - List.length results
  done;
  !res

(** Context for SMT translation, providing information on:
    - the Squirrel formulas being translated (e.g. table, system expression);
    - the SMT formulas (declared symbols and variables);
    - the translation mode. *)
type context = {
  env : Env.t;
  table : Symbols.table;
  system : SystemExpr.fset option;

  int_export : Why3.Theory.namespace;
  tm_export : Why3.Theory.namespace;

  int_leq_symb : Why3.Term.lsymbol;
  int_geq_symb : Why3.Term.lsymbol;
  int_lt_symb : Why3.Term.lsymbol;
  int_gt_symb : Why3.Term.lsymbol;

  leq_symb : Why3.Term.lsymbol;
  happens_symb : Why3.Term.lsymbol;
  init_symb : Why3.Term.lsymbol;
  pred_symb : Why3.Term.lsymbol;
  macro_cond_symb : Why3.Term.lsymbol;
  choose_symbs : (int, Why3.Term.lsymbol list) Hashtbl.t;
  msg_ty : Why3.Ty.ty;
  ts_ty : Why3.Ty.ty;
  index_ty : Why3.Ty.ty;
  int_ty : Why3.Ty.ty;

  vars : Vars.var list;

  ty_tbl : (string, Why3.Ty.tysymbol) Hashtbl.t;
  tyvar_tbl : (Ident.ident, Why3.Ty.tvsymbol) Hashtbl.t;
  actions_tbl : (string, Why3.Term.lsymbol * int) Hashtbl.t;
  vars_tbl : (int,Why3.Term.term) Hashtbl.t;
  functions_tbl : (string, Why3.Term.lsymbol * Why3.Ty.tvsymbol list) Hashtbl.t;
  macros_tbl : (string, Why3.Term.lsymbol * Symbols.macro) Hashtbl.t;
  names_tbl : (string, Why3.Term.lsymbol) Hashtbl.t;
  (* Hashtbl to store the terms translated opaquely.
     If a term has already been translated with the same context of
     free variables, then we reuse the same opaque translation. *)
  unsupp_tbl : (Term.term*(Why3.Term.term list), Why3.Term.lsymbol) Hashtbl.t;
  (* Why3 theory under construction. *)
  theory : Why3.Theory.theory_uc ref;

  fresh : int ref;
  poly : bool;
}

(* Custom fresh IDs;
   for some reason there were issues when relying only on Why3.Ident.id_fresh. *)
let id_fresh context name =
  context.fresh:=!(context.fresh)+1;
  Why3.Ident.id_fresh (name ^ "_" ^(string_of_int !(context.fresh)))

exception InternalError

let context_init ~poly tm_theory evars sqenv table system =
  let int_theory = try
      Why3.Env.read_theory env ["int"] (String.capitalize_ascii "int")
    with
    | Why3.Env.LibraryConflict _ | Why3.Env.LibraryNotFound _
    | Why3.Env.AmbiguousPath   _ | Why3.Env.TheoryNotFound  _ ->
      Format.printf "SMT: error while loading SMT theory file\n";
      raise InternalError
  in
  let tm_export = tm_theory.Why3.Theory.th_export
  and int_export = int_theory.Why3.Theory.th_export in
  let index_symb = Why3.Theory.ns_find_ts tm_export ["index"]
  and msg_symb = Why3.Theory.ns_find_ts tm_export ["message"]
  and ts_symb = Why3.Theory.ns_find_ts tm_export ["timestamp"]
  and int_symb = Why3.Theory.ns_find_ts tm_export ["int"];
  and theory =
    ref (Why3.Theory.use_export
        (Why3.Theory.create_theory (Why3.Ident.id_fresh "MyTheory"))
        tm_theory
    )
  in
  let choose_tbl = Hashtbl.create 12 in
  Hashtbl.add choose_tbl 1 [(Why3.Theory.ns_find_ls tm_export ["choose"])];
  {
    env = sqenv;
    table = table;
    system = system;

    int_export = int_export;
    tm_export = tm_export;

    int_leq_symb = Why3.Theory.ns_find_ls int_export ["infix <="];
    int_geq_symb = Why3.Theory.ns_find_ls int_export ["infix >="];
    int_lt_symb = Why3.Theory.ns_find_ls int_export ["infix <"];
    int_gt_symb = Why3.Theory.ns_find_ls int_export ["infix >"];

    leq_symb     = Why3.Theory.ns_find_ls tm_export ["infix <~"];
    happens_symb = Why3.Theory.ns_find_ls tm_export ["happens"];
    init_symb    = Why3.Theory.ns_find_ls tm_export ["init"];
    pred_symb    = Why3.Theory.ns_find_ls tm_export ["pred"];
    macro_cond_symb  = Why3.Theory.ns_find_ls tm_export ["macro_cond"];
    choose_symbs = choose_tbl;
    msg_ty   = Why3.Ty.ty_app msg_symb [];
    ts_ty    = Why3.Ty.ty_app ts_symb [];
    index_ty = Why3.Ty.ty_app index_symb [];
    int_ty = Why3.Ty.ty_app int_symb [];
    vars = evars;
    ty_tbl = Hashtbl.create 12;
    tyvar_tbl = Hashtbl.create 12;
    actions_tbl = Hashtbl.create 12;
    vars_tbl = Hashtbl.create 193;
    functions_tbl = Hashtbl.create 12;
    macros_tbl = Hashtbl.create 12;
    names_tbl = Hashtbl.create 12;
    unsupp_tbl = Hashtbl.create 12;

    theory = theory;
    fresh = ref 0;
    poly = poly;
  }

(* Adds a new type symbol to the symbol table and the theory
  the first time it is seen. *)
let add_type context s =
  let ts = Why3.Ty.create_tysymbol (id_fresh context s) [] NoDef in
  context.theory := Why3.Theory.add_ty_decl !(context.theory) ts;
  Hashtbl.add context.ty_tbl s ts;
  ts

(* Type conversion from Squirrel to Why3.
 The internal error raised is notably used
 to know when to translate in an opaque way. *)

let rec convert_type context = function
  | Type.Message -> context.msg_ty
  | Type.Timestamp -> context.ts_ty
  | Type.Boolean -> Why3.Ty.ty_bool
  | Type.Tuple l -> Why3.Ty.ty_tuple (List.map (convert_type context) l)
  | Type.Index -> context.index_ty
  | Type.TConstr ((ns,t),args)
      when Symbols.s_path_to_string (ns,t) = "int" ->
      assert (args=[]);
      context.int_ty
  | Type.TConstr ((ns,t),args)
      when Symbols.s_path_to_string (ns,t) = "string" ->
      assert (args=[]);
      Why3.Ty.ty_str
  | Type.TConstr ((ns,t),args) -> begin
    if args <> [] then raise InternalError; (* FEAT: support type arguments *)
    let s = Symbols.s_path_to_string (ns,t) in
    try
      Why3.Ty.ty_app (Hashtbl.find context.ty_tbl s)  []
    with Not_found -> Why3.Ty.(ty_app (add_type context s) [])
    end
  | Type.TVar v -> if context.poly then
      try
        Why3.Ty.ty_var (Hashtbl.find context.tyvar_tbl v)
      with Not_found ->
        let t = Why3.Ty.tv_of_string (Ident.to_string v) in
        Hashtbl.add context.tyvar_tbl v t;
        Why3.Ty.ty_var t
    else
      raise InternalError
  | Type.Fun (t1,t2) ->
    Why3.Ty.ty_func (convert_type context t1) (convert_type context t2)
  | Type.TUnivar _ -> raise InternalError

(** {2 Translation} *)

open Why3.Term

let find_fn context f =
  Hashtbl.find context.functions_tbl (path_to_string f)

(* Opaque translation of unsupported terms. *)
let unsupported_term context fmla str =
  let var_list =
    List.sort
      Stdlib.compare
      (Hashtbl.fold (fun _ x acc -> x::acc) context.vars_tbl []) in
  let symb = try Hashtbl.find context.unsupp_tbl (fmla, var_list)
    with Not_found -> begin let s =
                              Why3.Term.create_fsymbol
                                (id_fresh context str)
                                (List.map t_type var_list)
                                (convert_type context (Term.ty fmla))
        in Hashtbl.add context.unsupp_tbl (fmla, var_list) s;
        context.theory := Why3.Theory.add_decl_with_tuples
            !(context.theory)
            (Why3.Decl.create_param_decl s);
        s
      end
  in
  (Why3.Term.t_app_infer symb var_list)

(* Given a function symbol and a list of Why3 terms, we return
   the list of types missing in our list of terms to get a total application *)
let missing_types symb terms =
  let term_types = List.map Why3.Term.t_type terms in
  Utils.List.drop (List.length term_types) symb.ls_args

(* Why3 makes a distinction between terms and formulas.
   These two functions allows us to go back and forth between terms and formulas. *)

(* Transforms a Why3 term to a formula if it was of type bool,
   else acts as the identity. *)
let wbool_to_wfmla t =
  if Term.ty t = Type.tboolean then Why3.Term.to_prop else (fun x -> x)

(* Transforms a Why3 formula to a boolean term. *)
let wfmla_to_wbool p = Why3.Term.(t_if p t_bool_true t_bool_false)

(* Creation of Why3 variables from Squirrel variables.
  The variable is added to the table*)
let create_var context v =
  let vsymb =
    create_vsymbol
      (id_fresh context (Vars.name v))
      (convert_type context (Vars.ty v)) in
  Hashtbl.add context.vars_tbl (Vars.hash v) (t_var vsymb);
  vsymb

(* Removes a variable from the table based on the hash of the Squirrel var *)
let rem_var context v = Hashtbl.remove context.vars_tbl (Vars.hash v)

(* Auxillary function to add fmla as an axiom in the theory. *)
let add_why_axiom context fmla name =
  context.theory := Why3.Theory.add_decl_with_tuples !(context.theory)
      (Why3.Decl.create_prop_decl
          Why3.Decl.Paxiom
          (Why3.Decl.create_prsymbol @@  name)
          fmla)


(* Declares new choose functions and the associated axioms for a given arity *)
let declare_choose context i =
  let ty_vars = (List.init i
    (fun k -> Why3.Ty.ty_var (Why3.Ty.tv_of_string ("a"^(string_of_int k)))))
  in let fun_ty =
    List.fold_right
      (fun ty acc -> Why3.Ty.ty_func ty acc)
      ty_vars Why3.Ty.ty_bool
  and args_vars =
    List.map
      (fun ty -> Why3.Term.create_vsymbol (id_fresh context "x") ty)
      ty_vars
  in let choose_symbs =
    List.init i
    (fun j ->
      Why3.Term.create_fsymbol
      (id_fresh context ("choose_"^(string_of_int i)^"_"^(string_of_int (j+1))))
      [fun_ty]
      (List.nth ty_vars j)
    )
  in context.theory :=
    List.fold_left
      (fun theory choose_symb ->
            Why3.Theory.add_decl_with_tuples theory
              (Why3.Decl.create_param_decl choose_symb))
      !(context.theory) choose_symbs;
  Hashtbl.add context.choose_symbs i choose_symbs;
  let axiom_choose = let open Why3.Term in
    let var_phi = create_vsymbol (id_fresh context "phi") fun_ty in
    let phi = t_var var_phi in
    t_forall_close [var_phi] []
      (t_if
        (List.fold_right
          (fun v acc -> t_exists_close [v] [] acc)
          args_vars
          (to_prop
            (t_func_app_beta_l
              phi
              (List.map t_var args_vars)
            )
          )
        )
        (to_prop (t_func_app_beta_l
          phi
          (List.map
            (fun choose_symb -> t_app_infer choose_symb [phi])
            choose_symbs)
        ))
        t_true
      )
  in add_why_axiom
    context axiom_choose
    (id_fresh context ("choose_def_"^(string_of_int i)));
  choose_symbs

(* Transforms a list of Squirrel terms to a list of Why3 terms. *)
let rec sqfmlas_to_wterms context terms =
  List.map
    (fun (t,b) ->  if b then (wfmla_to_wbool t) else t)
    (List.map
        (fun t -> ((sqterm_to_wfmla context) t, Term.ty t=Type.tboolean))
        terms
    )

(* Main translation function. It converts a Squirrel term to a Why3 term
   (or formula if its type is bool). *)
and sqterm_to_wfmla context : Term.term -> Why3.Term.term = fun fmla ->
  let open Term in
  let open Why3.Term in
  (wbool_to_wfmla fmla) (match fmla with
    | Term.Int i ->
      let i = Why3.BigInt.of_string (Z.to_string i) in
      Why3.Term.t_int_const i

    | Term.String s -> Why3.Term.t_string_const s

    | Term.Var v when Term.ty fmla = Type.tboolean ->
      begin try to_prop (Hashtbl.find context.vars_tbl (Vars.hash v)) with
        | Not_found -> raise InternalError
      end
    | Var v ->
      begin try Hashtbl.find context.vars_tbl (Vars.hash v) with
        | Not_found -> raise InternalError
      end
    | Term.Fun  (symb,applied_ty) ->
      begin match symb with
        | _ when symb=f_false -> t_false
        | _ when symb=f_true ->  t_true
        | _
          when (Symbols.OpData.get_data symb context.table).ftype.fty_vars <> []
            && not context.poly
          -> unsupported_term context fmla "unsupp_poly"
        | _ ->
          begin match find_fn context symb with
              | f,var_list -> let remaining_types = missing_types f [] in
              t_app_partial f [] remaining_types
                (if f.ls_value = None then
                    None
                  else
                    begin
                      let subst_out = List.fold_left2
                        (fun acc tyv ty ->
                        Why3.Ty.Mtv.add tyv (convert_type context ty) acc)
                          Why3.Ty.Mtv.empty
                          var_list
                          applied_ty.ty_args
                      in
                      Some (Why3.Ty.(ty_inst subst_out (Option.get f.ls_value)))
                    end
                )
              | exception Not_found ->
                unsupported_term context fmla "unsupp_fun_not_found"
          end
      end
    (* For function applications, we need to handle separately
       the boolean connectives and the functions where the translation
       varies depending on the type of the terms. *)
    | Term.App (Fun (symb,applied_ty),terms) ->
      begin match terms with
        | [f] when symb=f_not -> t_not (sqterm_to_wfmla context f)
        | [f1;f2] when symb=f_and ->
          t_and (sqterm_to_wfmla context f1) (sqterm_to_wfmla context f2)
        | [f1;f2] when symb=f_or ->
          t_or (sqterm_to_wfmla context f1) (sqterm_to_wfmla context f2)
        | [f1;f2] when symb=f_impl ->
          t_implies (sqterm_to_wfmla context f1) (sqterm_to_wfmla context f2)
        | [f1;f2] when symb=f_iff ->
          t_iff (sqterm_to_wfmla context f1) (sqterm_to_wfmla context f2)
        | [t1;t2] when symb = f_eq ->
          if Term.ty t1 = Type.tboolean then
            t_iff (sqterm_to_wfmla context t1) (sqterm_to_wfmla context t2)
          else
            if Term.ty t1 = Type.ttimestamp then
              Why3.Term.t_equ
                (sqterm_to_wfmla context t1)
                (sqterm_to_wfmla context t2)
            else
            t_equ (sqterm_to_wfmla context t1) (sqterm_to_wfmla context t2)
      | [t1;t2] when symb = f_neq -> if Term.ty t1 = Type.tboolean then
        t_not (t_iff (sqterm_to_wfmla context t1) (sqterm_to_wfmla context t2))
        else
          (if Term.ty t1 = Type.ttimestamp then
          t_not
            (Why3.Term.t_equ (sqterm_to_wfmla context t1) (sqterm_to_wfmla context t2))
          else
          t_not (t_equ (sqterm_to_wfmla context t1) (sqterm_to_wfmla context t2) ))
      | [t1;t2] when symb = f_leq && (Term.ty t1 = Type.ttimestamp) ->
        t_app_infer
          context.leq_symb
          [sqterm_to_wfmla context t1;sqterm_to_wfmla context t2]
      | [t1;t2] when symb = f_geq && (Term.ty t1 = Type.ttimestamp) ->
        t_app_infer
          context.leq_symb
          [sqterm_to_wfmla context t2;sqterm_to_wfmla context t1]
      | [t1;t2] when symb = f_lt && (Term.ty t1 = Type.ttimestamp) ->
            t_and
              (t_app_infer
                context.leq_symb
                [sqterm_to_wfmla context t1;sqterm_to_wfmla context t2]
            )
            (t_not @@ Why3.Term.t_equ
                (sqterm_to_wfmla context t1) (sqterm_to_wfmla context t2)
            )
        | [t1;t2] when symb = f_gt && (Term.ty t1 = Type.ttimestamp) ->
          t_and
            (t_app_infer
                context.leq_symb
                [sqterm_to_wfmla context t2;sqterm_to_wfmla context t1]
            )
            (t_not @@ Why3.Term.t_equ
                (sqterm_to_wfmla context t2) (sqterm_to_wfmla context t1)
            )

        | [t1;t2] when symb = f_leq && (Term.ty t1) = Type.tint ->
          t_app_infer
            (context.int_leq_symb)
            [sqterm_to_wfmla context t1;sqterm_to_wfmla context t2]
        | [t1;t2] when symb = f_geq && (Term.ty t1) = Type.tint ->
          t_app_infer
            (context.int_geq_symb)
            [sqterm_to_wfmla context t1;sqterm_to_wfmla context t2]
        | [t1;t2] when symb = f_lt && (Term.ty t1) = Type.tint ->
          t_app_infer
            (context.int_lt_symb)
            [sqterm_to_wfmla context t1;sqterm_to_wfmla context t2]
        | [t1;t2] when symb = f_gt && (Term.ty t1) = Type.tint ->
          t_app_infer
            (context.int_gt_symb)
            [sqterm_to_wfmla context t1;sqterm_to_wfmla context t2]

        | [cond;f1;f2] when symb=f_ite ->
          t_if (sqterm_to_wfmla context cond)
            (sqterm_to_wfmla context f1)
            (sqterm_to_wfmla context f2)
        | _ when
            (Symbols.OpData.get_data symb context.table).ftype.fty_vars <> []
            && not context.poly
          -> unsupported_term context fmla "unsupp_poly"
        | _ ->
          begin match find_fn context symb with
              | f,var_list -> let wterms = sqfmlas_to_wterms context terms  in
              let remaining_types = missing_types f wterms in
              t_app_partial
                f
                wterms
                remaining_types
                (if f.ls_value = None then
                    None
                  else
                    begin
                      let subst_out = List.fold_left2
                        (fun acc tyv ty ->
                        Why3.Ty.Mtv.add tyv (convert_type context ty) acc)
                          Why3.Ty.Mtv.empty
                          var_list
                          applied_ty.ty_args
                      in
                      Some (Why3.Ty.(ty_inst subst_out (Option.get f.ls_value)))
                    end
                )
            | exception Not_found ->
              unsupported_term context fmla "unsupp_fun_not_found"
          end
      end
    | Term.App (f,terms) ->
      let wf = (sqterm_to_wfmla context f) in
      let wterms = (sqfmlas_to_wterms context terms) in
      Why3.Term.t_func_app_beta_l
        wf
        wterms
    | Term.Proj (i,t) ->
      begin match (Term.ty t) with
        | Type.Tuple l ->
          let pat_list,len,v =
            List.fold_left
              (fun (acc,j,v) ty ->
                let ty' = convert_type context ty in
                if i=j then
                  (* Create a temp var symbol used for pattern matching. *)
                  let v' =
                    Why3.Term.create_vsymbol ((id_fresh context ("temp"))) ty'
                  in
                  (pat_as (pat_wild ty') v' :: acc, j+1, Some v')
                else
                  (pat_wild ty' :: acc, j+1, v))
              ([],1,None)
              l
          in
          let pat_list = List.rev pat_list in
          Why3.Term.t_case_close
            (sqterm_to_wfmla context t)
            [pat_app
              (fs_tuple (len-1))
              pat_list
              (Why3.Ty.ty_tuple (List.map (convert_type context) l)),
             t_var (Option.get v)]

        | _ -> assert false
      end
    | Term.Quant (ForAll, vs, f) ->
      sqterm_to_wfmla_q context t_forall_close vs f fmla
    | Term.Quant (Exists, vs, f) ->
      sqterm_to_wfmla_q context t_exists_close vs f fmla
    | Term.Quant (Seq,vs,f) | Term.Quant (Lambda,vs,f) ->
      sqterm_to_wfmla_q context t_lambda vs f fmla
    | Action (a,indices) ->
      t_app_infer (fst(Hashtbl.find context.actions_tbl (path_to_string a)))
        (sqfmlas_to_wterms context indices)
    | Macro (ms,l,ts) ->
      begin match Hashtbl.find context.macros_tbl (path_to_string ms.s_symb) with
        | m,_ ->
          t_app
            m
            (sqfmlas_to_wterms context l @
              (if ts = Term.mk_unit then [] else [sqterm_to_wfmla context ts]))
            (if m.ls_value = None then
              None
            else
              Some (convert_type context (Term.ty fmla)))
        | exception Not_found ->
          unsupported_term context fmla "unsupp_macro_not_found"
      end
    | Name (ns,args) ->
      t_app
        (Hashtbl.find context.names_tbl (path_to_string ns.s_symb))
        (sqfmlas_to_wterms context args)
        (Some (convert_type context (Term.ty fmla)))

    | Diff  _ -> unsupported_term context fmla "diff"
    | Find (vars,cond,t,e) ->
      let choose_symbs = match Hashtbl.find context.choose_symbs (List.length vars) with
        | choose_symbs -> choose_symbs
        | exception Not_found -> declare_choose context (List.length vars)
      in let why_cond =
        (sqterm_to_wfmla context (mk_exists vars cond))
      in
      let why_vars = List.map (create_var context) vars in
      let why_then_core = sqterm_to_wfmla context t in
      List.iter (rem_var context) vars;
      let why_then =
        let fun_cond = sqterm_to_wfmla context (mk_lambda vars cond) in
        List.fold_left2
        (fun acc v choose ->
          t_let_close v
          (t_app_infer choose [fun_cond])
          acc
        )
        why_then_core
        why_vars choose_symbs
      in
      t_if why_cond why_then (sqterm_to_wfmla context e)
    | Tuple l -> t_tuple (sqfmlas_to_wterms context l)

    | Let (v,t1,t2) ->
      let let_as_quant qv _ subfmla =
        t_let_close(List.hd qv) (List.hd (sqfmlas_to_wterms context [t1])) subfmla
      in
      sqterm_to_wfmla_q
        context let_as_quant [v] t2 fmla

  )

(* Auxiliary function to handle quantified formulas. *)
and sqterm_to_wfmla_q context quantifier vs f fmla=
  (* NOTE: here we use the fact that OCaml hashtables can have multiple
   *       bindings, and the newer ones shadow the older ones
   * thus we can use Hashtbl.(add|remove) to handle bound variable scope. *)
  (* If we quantify over an unsupported variable,
     we translate the quantifier opaquely.
     This could be done more precisely by only keeping the supported variables
     and translating opaquely when encountering the undeclared variable. *)
  let quantified_vars = try
      Some (List.map
          (fun v ->
            (create_var context v))
          vs
      )
    with InternalError -> None
  in
  match quantified_vars with
    | None ->
      List.iter (rem_var context) vs;
      unsupported_term context fmla "unsupported_quant"
    | Some qv ->
      (* At this stage the variables are added to the scope, we can recurse *)
      try
        let subfmla = sqterm_to_wfmla context f in
        (* and then cleanup. *)
        List.iter (rem_var context) vs;
        quantifier qv [] subfmla
      with InternalError ->
        List.iter (rem_var context) vs;
        unsupported_term context fmla "unsupported_quant"

(* Checks the following invariant :
   the type of the translated term is equal to the translated type of the term *)
let sqterm_to_wfmla context fmla =
  (* Calls the previously defined recursive translation *)
  let wfmla = sqterm_to_wfmla context fmla
  and sqty = (convert_type context (Term.ty fmla)) in
  if sqty = Why3.Ty.ty_bool then
    (* If the term is a boolean,
       we want to check that the translation is a prop (not a term) *)
    Why3.Term.t_prop wfmla
  else begin
    assert (Why3.Term.t_type wfmla = (convert_type context (Term.ty fmla)));
    wfmla
  end

(* Fill symbol tables. *)
let add_actions context =
  if context.system <> None then (
    SystemExpr.iter_descrs context.table (Option.get context.system)
      (fun descr ->
          if descr.name <> Symbols.init_action then
            let str = path_to_string descr.name in
            let symb_act = Why3.Term.create_fsymbol
                (id_fresh context str)
                (List.init
                    (List.length descr.indices)
                    (fun _ -> context.index_ty))
                context.ts_ty
            in
            Hashtbl.add
              context.actions_tbl
              str
              (symb_act,List.length descr.indices)));
  context.theory :=
    Hashtbl.fold
      (fun _ (symb,_) theory ->
            Why3.Theory.add_decl_with_tuples
              theory
              (Why3.Decl.create_param_decl symb))
      context.actions_tbl !(context.theory);
  Hashtbl.add
    context.actions_tbl
    Symbols.(path_to_string init_action)
    (context.init_symb,0)

let add_var context =
  let add_tbl_var tbl ty var=
    let symb =
      Why3.Term.create_vsymbol (id_fresh context (Vars.name var)) (ty) in
    Hashtbl.add tbl (Vars.hash var) (t_var symb);
    symb
  in
  List.filter_map
    (fun var ->
        try
          Some (add_tbl_var
              context.vars_tbl
              (convert_type context (Vars.ty var))
              var
          )
        with InternalError -> None
    )
    context.vars

(* Checks if a type variable is present in a type *)
let rec check_type ty var = match ty with
  | Type.TVar v -> var = v
  | Type.Fun (t1,t2) -> (check_type t1 var) || (check_type t2 var)
  | Type.Tuple tl ->
    List.fold_left (fun acc t -> (check_type t var)||acc) false tl
  | _ -> false

(* Checks if a type variable is present in a list of types *)
let check_types tylist var =
  List.fold_left
    (fun acc ty -> acc || (check_type ty var)) false tylist

(* Add all function/predicate symbols that are neither names nor macros. *)
let add_functions context =
  Symbols.Operator.iter
    (fun fname _ ->
      let data = Symbols.OpData.get_data fname context.table in
      let ftype = data.ftype in
      let str = path_to_string fname in
      (* We do not declare boolean connectives,
        instead we will use Why3 builtin connectives. *)
      let boolean_connectives =
        [Symbols.fs_or; Symbols.fs_and; Symbols.fs_true;
          Symbols.fs_false; Symbols.fs_iff; Symbols.fs_impl; Symbols.fs_not]
      in
      (* We check if every type variable is really present
        in the type of the function. Else, the translation does not support it. *)
      let tyvar_used =
        let fty_args_out = ftype.fty_out::ftype.fty_args in
        List.fold_left
          (fun acc var -> acc && (check_types fty_args_out var))
          true
          ftype.fty_vars
      in
      if not (List.mem fname boolean_connectives) && tyvar_used
      then begin
        try
          let symb =
            Why3.Term.create_fsymbol
              (id_fresh context str)
              (List.map
                (fun t -> convert_type context t)
                ftype.fty_args)
              (convert_type context ftype.fty_out)
          in
          Hashtbl.add
            context.functions_tbl str
            (symb, List.map (Hashtbl.find context.tyvar_tbl) ftype.fty_vars)
        with InternalError ->
          if smt_debug then
            Format.printf "Cannot declare %s : %a@." str Type.pp_ftype ftype
      end
    )
  context.table;
  context.theory :=
    Hashtbl.fold
      (fun _ (symb,_) theory ->
        Why3.Theory.add_decl_with_tuples 
          theory
          (Why3.Decl.create_param_decl symb)
      )
      context.functions_tbl !(context.theory);
  (* Some builtin functions are declared twice, this is not an issue
     as the new mapping will replace the previous one. *)
  List.iter
    (fun (fname,symb) ->
      Hashtbl.add context.functions_tbl
        (path_to_string fname)
        (Why3.Theory.ns_find_ls context.tm_export [symb],[])
    )
    [(Symbols.fs_xor,"xor");
      (Symbols.fs_pred,"pred");
      (Term.f_happens,"happens");
    ];
  let choose_symb = List.hd (Hashtbl.find context.choose_symbs 1) in
  Hashtbl.add
    context.functions_tbl "choose"
    (choose_symb, match (oget choose_symb.ls_value).ty_node with
      | Tyvar v -> [v]
      | _ -> assert false
    );
  List.iter
    (fun (fname,symb) ->
      Hashtbl.add 
        context.functions_tbl
        (fname)
        (Why3.Theory.ns_find_ls context.int_export [symb],[])
    )
    [("Int_+","infix +");
      ("Int_-","infix -");
      ("Int_*","infix *");
      ("Int_opp","prefix -");
    ]



(* Add all supported macro symbols. *)
let add_macros context =
  Symbols.Macro.iter (fun mn _ ->
    let def = Symbols.get_macro_data mn context.table in
    let str = path_to_string mn in
    let symb params rec_type ty =
      Why3.Term.create_fsymbol
        (id_fresh context str)
        (params @ rec_type)
        ty
    in
    match str with
      | "Classic_cond" ->
        Hashtbl.add context.macros_tbl str (context.macro_cond_symb,mn)
      | _ ->
        if (not(TConfig.smt_quantum context.table) &&
            (String.starts_with ~prefix:"Quantum" str)) ||
           (not(TConfig.smt_classic context.table) &&
            (String.starts_with ~prefix:"Classic" str))
        then () else
        begin try
            let params,rec_type,ty = match def with
              | General d ->
                begin
                  match Macros.get_general_macro_data d with
                  | Structured d ->
                    let params =
                      List.map
                        (fun v -> convert_type context (Vars.ty v))
                        d.params
                    in
                    if d.dist_param = None then
                      params,[],(convert_type context d.ty)
                    else
                      let ty = (oget d.dist_param).ty in
                      params,
                      [convert_type context ty], (convert_type context d.ty)
                  | ProtocolMacro `Output ->
                    [],[context.ts_ty],convert_type context Type.tmessage
                  | ProtocolMacro `Cond ->
                    [],[context.ts_ty],convert_type context Type.tboolean
                end
              | State(i,t,_,_) | Global(i,t,_) ->
                List.init i (fun _ -> context.index_ty),
                [context.ts_ty],convert_type context t
            in
            Hashtbl.add context.macros_tbl str (symb params rec_type ty, mn)
          with InternalError ->
            if smt_debug then Format.printf "Cannot declare macro %s@." str
        end
    ) context.table;

  context.theory:= Hashtbl.fold (fun _ (symb,_) theory ->
      begin try
          Why3.Theory.add_decl_with_tuples
            theory
            (Why3.Decl.create_param_decl symb)
        with _ -> theory
      end
    ) context.macros_tbl !(context.theory)

let add_names context =
  Symbols.Name.iter (fun name _ ->
    let def = Symbols.get_name_data name context.table in
    let str = path_to_string name in
    begin try
        let symb =
          Why3.Term.create_fsymbol
            (id_fresh context str)
            (List.fold_left
                (fun acc t -> acc@[convert_type context t])
                [] def.n_fty.fty_args
            )
            (convert_type context def.n_fty.fty_out)
        in
        Hashtbl.add context.names_tbl str (symb)
      with InternalError ->
        if smt_debug then Format.printf "Cannot declare %s@." str
    end
  ) context.table;
  context.theory:= Hashtbl.fold
      (fun _ (symb) theory ->
            Why3.Theory.add_decl_with_tuples
              theory
              (Why3.Decl.create_param_decl symb))
      context.names_tbl !(context.theory)

(* Creates a list of variable matching the types of ty_list *)
let rec vsymbol_list context c ty_list = match ty_list with
  | [] -> []
  | t::q ->
    (Why3.Term.create_vsymbol
        (id_fresh context c) t)::(vsymbol_list context c q)

(* Returns the Why3 Term testing the equality of  two lists of terms. *)
let rec equal_lists context tl1 tl2 = match tl1,tl2 with
  | [],[] -> Why3.Term.t_true
  | [],_ | _,[] -> Format.printf "Uneven arities@.";raise InternalError
  | h1::t1,h2::t2 -> match h1.t_ty with
    | Some t when t=context.ts_ty -> Why3.Term.(t_and
          (Why3.Term.t_equ h1 h2) (equal_lists context t1 t2))
    | _ -> Why3.Term.(t_and (t_equ h1 h2) (equal_lists context t1 t2))


(* Timestamp related axioms :
   injectivity, surjectivity and dependencies between timestamps. *)
let add_timestamp_axioms context =
  let distinct_actions_axioms = Hashtbl.fold (fun k (a,n) acc ->
      Hashtbl.fold (fun k' (a',n') acc' ->
        if k < k'
        then let l1,l2 =
               vsymbol_list
                 context
                 "i"
                 (List.init n (fun _ -> context.index_ty)),
               vsymbol_list
                 context
                 "j"
                 (List.init n' (fun _ -> context.index_ty))
          in
          let tl1,tl2 =
            List.map Why3.Term.t_var l1,List.map Why3.Term.t_var l2
          in
          Why3.Term.(t_forall_close l1 []
              (t_forall_close l2 []
                    (t_implies
                        (t_app_infer context.happens_symb [t_app_infer a tl1])
                        (t_implies
                            (t_app_infer
                                context.happens_symb
                                [t_app_infer a' tl2]
                            )
                            (t_not
                                (Why3.Term.t_equ
                                    (t_app_infer a tl1)
                                    (t_app_infer a' tl2)
                                )
                            )
                        )
                    )
              )
          )::acc'
        else acc'
      ) context.actions_tbl acc
    ) context.actions_tbl []

  and injective_timestamps =
    let axiom_injective_ts a n =
      let l1,l2 =
        vsymbol_list
          context
          "i"
          (List.init n (fun _ -> context.index_ty)),
        vsymbol_list
          context
          "j"
          (List.init n (fun _ -> context.index_ty))
      in
      let tl1,tl2 = List.map Why3.Term.t_var l1,List.map Why3.Term.t_var l2 in
      Why3.Term.(t_forall_close l1 [](t_forall_close l2 []
          (t_implies
              (t_app_infer context.happens_symb [t_app_infer a tl1])
              (t_implies (t_app_infer context.happens_symb [t_app_infer a tl2])
                    (t_implies
                        (Why3.Term.t_equ (t_app_infer a tl1) (t_app_infer a tl2))
                        (equal_lists context tl1 tl2)
                    )
              )
          )
        ))
    in

    Hashtbl.fold (fun _ (a,n) acc ->
      (axiom_injective_ts a n)::acc
    ) context.actions_tbl []
  in
  (* Rem: we use "=" instead of "~~" since we assume that the timestamps happen
     Case disjunction for timestamps. *)
  let cases t _ (a,n) fml =
    let l1 =
      vsymbol_list
        context
        "i"
        (List.init n (fun _ -> context.index_ty))
    in let tl1 = List.map Why3.Term.t_var l1 in
    Why3.Term.(t_or (t_exists_close l1 [](t_equ (t) (t_app_infer a tl1))) fml)
  in

  let case_quantified =
    let t_vsymb = Why3.Term.create_vsymbol
        (id_fresh context "t")
        context.ts_ty
    in
    let t = Why3.Term.t_var t_vsymb in
    Why3.Term.t_forall_close [t_vsymb] [] (
      Why3.Term.t_implies
        (Why3.Term.t_app_infer context.happens_symb [t])
        (Hashtbl.fold (cases t) context.actions_tbl (Why3.Term.t_false)))
  in

  (* Add axioms for action dependencies to above mutable list. *)
  (* "mk_depends_lemma" function from lemma.ml. *)
  let depends =
    SystemExpr.fold_descrs
      (fun descr1 acc -> SystemExpr.fold_descrs (fun descr2 acc' ->
            if descr1.name <> Symbols.init_action &&
               Action.depends
                 (Action.get_shape_v descr1.action)
                 (Action.get_shape_v descr2.action)
            then begin
              let a2 =
                Term.mk_action descr2.name (Term.mk_vars descr2.indices)
              in
              let a1 =
                let indices =
                  List.take (List.length descr1.indices) descr2.indices
                in
                Term.mk_action descr1.name (Term.mk_vars indices)
              in
              let axiom =
                Term.mk_forall ~simpl:false descr2.indices
                  (Term.mk_impls
                      [Term.mk_happens a2]
                      (Term.mk_lt a1 a2))
              in
              (sqterm_to_wfmla context axiom)::acc'
            end
            else acc'
          ) context.table (Option.get context.system) acc
      )
      context.table (Option.get context.system) []
  in
  (* Add axioms for action exclusion to above mutable list. *)
  (* "mk_mutex_lemma" function from lemma.ml. *)
  let mutex =
    SystemExpr.fold_descrs
      (fun descr1 acc -> SystemExpr.fold_descrs (fun descr2 acc' ->
            let shape1 = Action.get_shape_v  descr1.action in
            let shape2 = Action.get_shape_v descr2.action in
            if descr1.name < descr2.name && (Action.mutex shape1 shape2)
            then begin
              (* number of common variables between mutually exclusives actions
                 of [descr] and [descr']. *)
              let i_common = Action.mutex_common_vars shape1 shape2 in
              let is_common, is_rem1  =
                List.takedrop i_common  descr1.indices
              in
              let _        , is_rem2 = List.takedrop i_common descr2.indices in

              let a1  = Term.mk_action
                  descr1.name (Term.mk_vars (is_common @ is_rem1))
              in let a2 = Term.mk_action
                     descr2.name (Term.mk_vars (is_common @ is_rem2))
              in let axiom =
                   Term.mk_forall ~simpl:false (is_common @ is_rem1 @ is_rem2)
                     (Term.mk_or
                         (Term.mk_not (Term.mk_happens a1))
                         (Term.mk_not (Term.mk_happens a2)))
              in
              (sqterm_to_wfmla context axiom)::acc'
            end
            else acc'
          ) context.table (Option.get context.system) acc
      )
      context.table (Option.get context.system) []

  in
    List.iter (fun (id_ax,ax) ->
    add_why_axiom context ax (id_fresh context id_ax)
  ) (List.map (fun x -> ("axiom_distinct", x))
      (distinct_actions_axioms)
    @ [("case_quantified", case_quantified)]
    @ (List.map (fun x -> ("axiom_depends", x))
        depends)
    @ (List.map (fun x -> ("axiom_injective", x))
        injective_timestamps)
    @ (List.map (fun x -> ("axiom_mutex", x))
        mutex)
  )

(* Returns the type of the nth type of a tuple type.
  Acts as the identity if the type given as argument is not a tuple. *)
let nth_tuple ty n = let open Why3.Ty in match ty.ty_node with
  | Tyapp (ts, tl) when is_ts_tuple ts ->
    List.nth tl n
  | _ -> ty

(* Simple equational axioms on cryptographic primitives. *)
let add_equational_axioms context =
  let axiom_pair =
    let vx = Why3.(Term.create_vsymbol (Ident.id_fresh "x")
        context.msg_ty) in
    let vy = Why3.(Term.create_vsymbol (Ident.id_fresh "y")
        context.msg_ty) in
    [(Symbols.fs_fst, vx); (Symbols.fs_snd, vy)]
    |> List.map (fun (proj, v) ->
      t_equ
        (t_app_infer
            (fst (find_fn context proj))
            [t_app_infer
                (fst (find_fn context Symbols.fs_pair))
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
    (* Cases taken from Completion.init_erules. *)
    | AEnc, [f1; f2] ->
      let dec, pk = (* From Completion.dec_pk. *)
        match Symbols.OpData.get_abstract_data f1 context.table,
          Symbols.OpData.get_abstract_data f2 context.table with
        | (ADec     , _), (PublicKey, _) -> f1, f2
        | (PublicKey, _), (ADec     , _) -> f2, f1
        | _ -> assert false
      in
      let dec_symb = fst (find_fn context dec)
      and pk_symb = fst (find_fn context pk)
      and enc_symb = fst (find_fn context fname) in
      let tm = nth_tuple (List.hd enc_symb.Why3.Term.ls_args) 0
      and tr = nth_tuple (List.hd enc_symb.Why3.Term.ls_args) 1
      and tk = List.hd pk_symb.Why3.Term.ls_args in
      (* We omit the check_zero_arities from Completion. *)
      (* dec(enc(m, r, pk(k)), k) -> m *)
      let vars =
        List.map (fun (str,ty) ->
          Why3.(Term.create_vsymbol (Ident.id_fresh str) ty)
        ) ["m",tm; "r",tr; "k",tk]
      in
      let (vm, vr, vk) = as_seq3 vars in
      let term =
        t_equ (t_app_infer dec_symb
            [Why3.Term.t_tuple [t_app_infer enc_symb (* fname = enc *)
                    [Why3.Term.t_tuple [t_var vm; t_var vr;
                          t_app_infer pk_symb
                            [t_var vk]]];
                  t_var vk]])
          (t_var vm) |> t_forall_close vars []
      in
      Some ("axiom_aenc", term)

    | SEnc, [sdec] ->
      (* dec(enc(m, r, k), k) -> m *)
      let sdec_symb = fst (find_fn context sdec)
      and enc_symb = fst (find_fn context fname) in
      let tm = nth_tuple (List.hd enc_symb.Why3.Term.ls_args) 0
      and tr = nth_tuple (List.hd enc_symb.Why3.Term.ls_args) 1
      and tk = nth_tuple (List.hd enc_symb.Why3.Term.ls_args) 2 in
      let vars =
        List.map (fun (str,ty) ->
          Why3.(Term.create_vsymbol (Ident.id_fresh str) ty)
        ) ["m",tm; "r",tr; "k",tk]
      in
      let vm, vr, vk = as_seq3 vars in
      let term =
        t_equ (t_app_infer sdec_symb
            [Why3.Term.t_tuple [t_app_infer enc_symb
                    [Why3.Term.t_tuple [t_var vm; t_var vr; t_var vk]];
                  t_var vk]])
          (t_var vm) |> t_forall_close vars []
      in
      Some ("axiom_senc", term)

    | CheckSign, [f1; f2] ->
      let msig, pk = (* From Completion.sig_pk. *)
        match Symbols.OpData.get_abstract_data f1 context.table,
          Symbols.OpData.get_abstract_data f2 context.table with
        | (Sign     , _), (PublicKey, _) -> f1, f2
        | (PublicKey, _), (Sign     , _) -> f2, f1
        | _ -> assert false
      in
      (* mcheck(m,msig(m, k), pk(k)) -> true *)
      let msig_symb = fst (find_fn context msig)
      and pk_symb = fst (find_fn context pk)
      and check_symb = fst (find_fn context fname) in
      let tm = nth_tuple (List.hd msig_symb.Why3.Term.ls_args) 0
      and tk = List.hd pk_symb.Why3.Term.ls_args in
      let vars =
        List.map (fun (str,ty) ->
          Why3.(Term.create_vsymbol (Ident.id_fresh str) ty)
        ) ["m",tm; "k",tk]
      in
      let vm, vk = as_seq2 vars in
      let term =
        Why3.Term.to_prop (t_app_infer check_symb
            [Why3.Term.t_tuple [t_var vm;t_app_infer msig_symb
                    [Why3.Term.t_tuple [t_var vm; t_var vk]];
                  t_app_infer pk_symb
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
  List.iter (fun (id_ax,ax) ->
    add_why_axiom context ax (id_fresh context id_ax)
  ) (equational_axioms)

(* Expansion of macros. *)
let sq_id_fresh s = Ident.fresh (Ident.create s)

(* Add the unfold of every macro. *)
let add_macro_axioms context =
  Hashtbl.iter (fun _ (_,mn) ->
    let m_symb = Macros.msymb context.table mn
    and str = path_to_string mn
    and def = Symbols.get_macro_data mn context.table in
    let params_vars, rec_arg_var = match def with
      | General d -> begin
          match Macros.get_general_macro_data d with
          | Structured d -> d.params,d.dist_param
          | _ -> [], Some (Vars.mk (sq_id_fresh "rec_arg") Type.ttimestamp)
        end
      | State (i,_,_,_) | Global (i,_,_) ->
        List.init i
          (fun i ->
             Vars.mk (sq_id_fresh ("ind_"^(string_of_int i))) Type.tindex
          ),
        Some (Vars.mk (sq_id_fresh "rec_arg") Type.ttimestamp)
    in
    let params_terms = List.map Term.mk_var params_vars in
    let rec_arg = match rec_arg_var with
      | None -> Term.mk_unit
      | Some v -> Term.mk_var v
    in
    let unfolded_l = Macros.unfold context.env m_symb params_terms rec_arg in
    let sqaxioms =
      match unfolded_l with
        | `Results l ->
          List.map
            (fun body ->
               Term.mk_forall
                 (if rec_arg_var <> None then
                    (oget rec_arg_var)::params_vars
                  else
                    params_vars)
                 (Term.mk_forall
                    body.Macros.vars
                    (Term.mk_impl
                       (Term.mk_and
                          (Term.mk_eq
                             rec_arg
                             (oget_dflt rec_arg body.Macros.pattern))
                          body.Macros.when_cond)
                       (Term.mk_eq
                          (Term.mk_macro m_symb params_terms rec_arg)
                          body.Macros.out))))
            l
        | `Unknown -> []
    in
    List.iter
      (fun fmla ->
        try
          let axiom = sqterm_to_wfmla context fmla in
          add_why_axiom context axiom (id_fresh context str)
        with InternalError -> ())
      sqaxioms)
  context.macros_tbl

(* Gets the total number of variables indexing a name to use for a quantifier.
Tuples are decomposed. *)
let rec calc_arity l = match l with
  | [] -> 0
  | (Type.Tuple t)::q -> (calc_arity t) + (calc_arity q)
  | _::q -> 1 + (calc_arity q)

(* For a list of sq types ty_list and a list of why3 terms (obtained from vars)
returns the list of why3 terms matching the types ty_list by creating
the appropriate tuples. Used to get the terms to which a name is applied
after creating vars based on the function calc_arity *)

let rec args_list ty_list var_list = match ty_list with
  | [] -> []
  | (Type.Tuple l)::q -> let n = calc_arity l in
    [t_tuple (args_list l (List.take n var_list))]
    @(args_list q (List.drop n var_list))
  | _::q -> [List.hd var_list]@(args_list q (List.tl var_list))

(* Injectivity of names. *)
let add_name_axioms context =
  let name_inj_axioms =
    Symbols.Name.fold (fun n1 _ acc1 ->
      let def1 = Symbols.get_name_data n1 context.table in
      Symbols.Name.fold (fun n2 _ acc2 ->
        begin try
          let def2 = Symbols.get_name_data n2 context.table in
          if
            def1.n_fty.fty_out = def2.n_fty.fty_out &&
            HighType.check_ty_info
              context.table
              def1.n_fty.fty_out
              Large
          then begin
            let ar1,ar2 =
              calc_arity def1.n_fty.fty_args,
              calc_arity def2.n_fty.fty_args
            in
            if n1 > n2 then acc2 else (* To avoid redundancy. *)
            let l1,l2 =
              vsymbol_list
                context
                "i"
                (List.init ar1 (fun _ -> context.index_ty)),
              vsymbol_list
                context
                "j"
                (List.init ar2 (fun _ -> context.index_ty))
            in
            let tl1,tl2 =
              List.map Why3.Term.t_var l1,
              List.map Why3.Term.t_var l2
            in
            let targ1,targ2 =
              args_list def1.n_fty.fty_args tl1,
              args_list def2.n_fty.fty_args tl2
            in
            let ineq = t_neq
                  (t_app_infer (Hashtbl.find context.names_tbl
                                  (path_to_string n1)) targ1)
                  (t_app_infer (Hashtbl.find context.names_tbl
                                  (path_to_string n2)) targ2) in
              t_forall_close (l1@l2) []
                (if n1 = n2
                  then t_implies (t_not (equal_lists context tl1 tl2)) ineq
                  else ineq)
              :: acc2
          end
          else acc2
          with Not_found -> acc2
        end)
      acc1 context.table)
    []
    context.table
  in
  let namelength_axioms = Symbols.Name.fold (fun n _ acc ->
    let def = Symbols.get_name_data n context.table in
    let name_ty = def.n_fty.fty_out in
    (* Namelength axioms are only added if the type has a fixed lenght *)
    if not @@ HighType.is_name_fixed_length context.table name_ty then
      acc
    else
      (* If it didn't exist before, we create the cst for the type's length *)
      let cst_name = "namelength_"^(Type.to_string name_ty) in
      let cst = match Hashtbl.find context.functions_tbl cst_name with
        | f,_ -> f
        | exception Not_found ->
          let cst =
            Why3.Term.create_fsymbol
              (Why3.Ident.id_fresh cst_name) [] context.msg_ty
          in Hashtbl.add context.functions_tbl cst_name (cst,[]); cst
      in let len_fun = match Hashtbl.find context.functions_tbl "len" with
        | f,_ -> f
        | exception Not_found -> assert false
      and n_why = Hashtbl.find context.names_tbl (path_to_string n)
      and ar = calc_arity def.n_fty.fty_args in
      let l =
        vsymbol_list
          context
          "i"
          (List.init ar (fun _ -> context.index_ty))
      in let tl = List.map Why3.Term.t_var l in
      let targ = args_list def.n_fty.fty_args tl in
      let ax = t_forall_close l []
        (t_equ
          (t_app_infer len_fun
            [t_app_infer n_why targ]
          )
          (t_app_infer cst [])
        )
      in ax::acc
    ) [] context.table
  in
  List.iter
    (fun (id_ax, ax) ->
       add_why_axiom context ax (id_fresh context id_ax))
    (List.map (fun x -> ("axiom_distinct", x)) name_inj_axioms);
  List.iter
    (fun (id_ax, ax) ->
      add_why_axiom context ax (id_fresh context id_ax))
    (List.map (fun x -> ("axiom_namelength", x)) namelength_axioms)

(* Check if the hint is valid in any system. *)
let local_stmt_valid_in_any_system (hint : Hint.smt_hint) =
  match (hint.system.set :> SE.exposed).cnt with
  | Var v ->
    let infos = List.assoc v hint.params.se_vars in
    infos = []
  | _ -> false

(* Add the hint to the theory if it is compatible with the system.
  A substitution is applied if needed. *)
let add_hint context system hint =
  let hint_system = hint.Hint.system.set
  and name = hint.Hint.name in
  if SE.subset_modulo context.table system hint_system then begin
    let subst_proj =
      let (_, s) =
        SE.mk_proj_subst
          ~strict:false ~src:hint_system ~dst:system
      in fun t -> Term.subst_projs ~project:true s t
    in let fmla = subst_proj hint.Hint.formula.Equiv.formula
    and name = hint.Hint.name in
    add_why_axiom context (sqterm_to_wfmla context fmla) (id_fresh context name);
  end
  else begin
    if local_stmt_valid_in_any_system hint then
      add_why_axiom
        context
        (sqterm_to_wfmla context hint.Hint.formula.Equiv.formula)
        (id_fresh context name);
  end
let build_task ~macro_axioms ~poly ~hint_tables env table system
    evars hypotheses hints conclusion tm_theory =
  let system_fset = match SystemExpr.to_fset system with
    | exception SystemExpr.(Error (_,Expected_fset)) -> None
    | fsys -> Some fsys
  in
  let context =
    context_init ~poly tm_theory evars env table system_fset
  in
  add_actions context;
  add_functions context;
  add_macros context;
  add_names context;
  add_equational_axioms context;
  List.iter
    (fun hint_table -> 
      List.iter
        (fun hint -> add_hint context system hint)
        (Utils.oget_dflt [] (Utils.Ms.find_opt hint_table hints))
    ) hint_tables;
  if macro_axioms then add_macro_axioms context;
  if system_fset<>None then add_timestamp_axioms context;
  add_name_axioms context;
  let top_level_var = add_var context in
  (* Converts hypotheses with 'and' at top level to two (or more) hypotheses. *)
  let rec convert_hypotheses hypotheses= match hypotheses with
    | [] -> []
    | t::q -> match Term.destr_and t with
      | Some (t1, t2) -> t1::(convert_hypotheses (t2::q))
      | None -> t::(convert_hypotheses q)
  in
  let decl = Why3.Decl.create_prop_decl
      Why3.Decl.Pgoal
      (Why3.Decl.create_prsymbol @@ id_fresh context "GOAL")
      (Why3.Term.t_forall_close top_level_var []
            (Why3.Term.t_not
                (Why3.Term.t_and
                    (Why3.Term.t_and_l
                        (List.filter_map
                            (fun h ->
                                try
                                  Some (sqterm_to_wfmla context h)
                                with InternalError -> None)
                            (convert_hypotheses hypotheses)))
                    (Why3.Term.t_not
                        (try sqterm_to_wfmla context conclusion with
                            InternalError -> Why3.Term.t_false)))))
  in
  let theory : Why3.Theory.theory_uc =
    let module Mid = Why3.Ident.Mid in
    let module Sid = Why3.Ident.Sid in
    let used_syms : Sid.t = Why3.Decl.get_used_syms_decl decl in
    let unknown_tsyms = Mid.set_diff used_syms !(context.theory).uc_known in
    Sid.fold
      (fun symb theory ->
          match Why3.Ty.is_ts_tuple_id symb with
          | Some n -> Why3.Theory.(use_export theory (tuple_theory n))
          | None -> theory
      )
      unknown_tsyms
      !(context.theory)
  in
  let task = Why3.Task.use_export None (Why3.Theory.close_theory theory) in
  Why3.Task.add_decl task decl


let unique_id =
  let id = ref 0 in
  fun () -> incr id ; !id

let is_valid
    ~macro_axioms ~timeout ~steps ~provers ~cmd_flag ~poly ~hint_tables
    sqenv table system evars hypotheses hints conclusion
  =
  if disable_smt then
    (Format.eprintf "SMT support disabled in JS.@.";
      false)
  else
  let theory = match load_theory env with
    | Some theory -> theory
    | None -> raise InternalError
  in
  let task =
    build_task
      ~poly
      ~macro_axioms ~hint_tables
      sqenv table system
      evars hypotheses hints conclusion
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
  run_all_async ~timeout ~steps ~provers ~cmd_flag task

(* Tactic registration. *)

let sequent_is_valid
    ~timeout ~steps ~provers ~cmd_flag ~poly ~hint_tables
    (s:TraceSequent.t)
  =
  let env = TraceSequent.env s in
  let table = env.table in
  let system = env.system.set in
  let evars = Vars.to_vars_list env.vars in
  let hypotheses =
    List.filter_map
      (function
        | _, Hyps.LHyp (Equiv.Local h) -> Some h
        | _, Hyps.LHyp (Equiv.(Global Atom (Reach {formula = f; bound = None})))
          -> Some f
        | id, Hyps.LDef (def_sys, def) ->
          let v = Vars.mk id (Term.ty def) in
          if SE.subset_modulo table system def_sys then begin
            let subst_proj =
              let (_, s) =
                SE.mk_proj_subst
                  ~strict:false ~src:def_sys ~dst:system
              in fun t -> Term.subst_projs ~project:true s t
            in Some (Term.mk_eq (Term.mk_var v) (subst_proj def))
          end
          else
            raise InternalError
        | _ -> None)
      (LowTraceSequent.Hyps.to_list s)
  and hints = Hint.get_smt_db table
  in
  let conclusion = LowTraceSequent.conclusion s in
  try is_valid ~timeout ~steps ~provers ~cmd_flag ~poly ~hint_tables
    env table system evars hypotheses hints conclusion
  with
  | e -> raise e

type parameters = {
  timeout : int;
  steps : int option;
  provers : (string*string) list;
  macro_axioms : bool (** [true] when macro axioms should be sent to solvers *);
  poly : bool;
  hint_tables: string list;
}

let default_prover =
  if disable_smt then []
  else
    let l =
      List.map
        (fun p ->
            Why3.Whyconf.(p.prover_name,p.prover_altern))
        (Why3.Whyconf.Mprover.keys why3_provers)
    in
    match l with
    | [] -> Tactics.(hard_failure (Failure "No SMT solvers detected"))
    | _ -> l

let default_parameters table = {
  timeout = 1;
  steps =
   if TConfig.smt_steps table <> 0 then
      Some (TConfig.smt_steps table) 
    else 
      None;
  provers = default_prover;
  macro_axioms = true;
  poly = true;
  hint_tables = ["default"];
}

let parse_prover_arg prover_alt =
  let add_dash s = if s = "AltErgo" then "Alt-Ergo" else s in
  let add_plus alt =
    if alt = "stringscounterexamples" then "strings+counterexamples" else alt in
  match String.split_on_char '_' prover_alt with
  | [p;alt] -> add_dash p, add_plus alt
  | [p] -> add_dash p, ""
  | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))

let parse_arg parameters = let open TacticsArgs in function

    (* Provers. *)
    | NList ({Location.pl_desc="prover"},[String_name {Location.pl_desc="All"}])
    | NList ({Location.pl_desc="provers"},[String_name {Location.pl_desc="All"}])
      ->
      let l =
        List.filter
          (fun (name,_) -> name <> "CVC4")
          (List.map
              (fun p -> Why3.Whyconf.(p.prover_name,p.prover_altern))
              (Why3.Whyconf.Mprover.keys why3_provers))
      in
      {parameters with provers = l}
    | NList ({Location.pl_desc="prover"},l)
    | NList ({Location.pl_desc="provers"},l) ->
      let process_prover provers {Location.pl_desc=prover_alt} =
        parse_prover_arg prover_alt :: provers
      in
      let l =
        List.map
          (function
            | String_name s -> s
            | _ -> Tactics.(hard_failure (Failure "expected a symbol")))
          l
      in
      { parameters with provers = List.fold_left process_prover [] l }

    (* Other flags. *)
    | NList ({Location.pl_desc="timeout"},
        [Int_parsed {Location.pl_desc=s}]) ->
      { parameters with timeout=s}
    | NList ({Location.pl_desc="steps"},
        [Int_parsed {Location.pl_desc=s}]) ->
      { parameters with steps=Some s}
    | NArg {Location.pl_desc="no_macros"} ->
      { parameters with macro_axioms = false }
    | NArg {Location.pl_desc="no_poly"} ->
      { parameters with poly = false }

    | NList ({Location.pl_desc="hint"},l) ->
      let l =
        List.map
          (function
            | String_name s -> s.Location.pl_desc
            | _ -> Tactics.(hard_failure (Failure "expected a symbol")))
          l
      in
      { parameters with hint_tables = "default"::l }

    | _ -> Tactics.(hard_failure (Failure "unrecognized argument"))

let parse_args args table =
  List.fold_left parse_arg (default_parameters table) args

let () =
  if not disable_smt then
    ProverTactics.register_general "smt"
      (fun args s sk fk ->
          let args = match args with
            | [Named_args_gen args] -> args
            | _ -> assert false
          in
          let s = match s with
            | Goal.Global _ ->
              Tactics.(hard_failure (Failure "SMT not available"))
            | Goal.Local s -> s
          in
          let {timeout;steps;
              provers;macro_axioms;poly;hint_tables} =
            parse_args args ((TraceSequent.env s).table)
          in
          let cmd_flag = match provers with
            | ["CVC5",_] -> "--enum-inst"
            | _ -> ""
          in if
            sequent_is_valid
              ~macro_axioms ~timeout
              ~steps ~provers ~cmd_flag ~poly ~hint_tables s
          then
            sk [] fk
          else
            fk (None, Tactics.Failure "SMT cannot prove sequent"))

let () =
  let provers = match Sys.getenv_opt "SMT_PROVERS" with
    | None -> ["CVC5",""]
    | Some s when s="All" ->
      List.filter
        (fun (name,_) -> name<>"CVC4")
        (List.map
            (fun p ->
                Why3.Whyconf.(p.prover_name,p.prover_altern))
            (Why3.Whyconf.Mprover.keys why3_provers)
        )
    | Some s -> List.map parse_prover_arg (String.split_on_char ':' s)
  in
  let flags = match Sys.getenv_opt "SMT_FLAGS" with
    | None -> [""]
    | Some s -> String.split_on_char ':' s
  in
  let benchmarks =
    match Sys.getenv_opt "SMT_BENCHMARKS" with
    | None -> []
    | Some s -> String.split_on_char ':' s
  in
  let poly =
    match Sys.getenv_opt "SMT_POLY" with
    | None  | Some "true" -> true
    | Some "false" -> false
    | _ ->
      Format.eprintf "Unknown polymorphism flag!@.";
      Format.eprintf "If set and non-empty, \
                      SMT_POLY must be true or false.@.";
      exit 1

  in
  let bench_name prover alt cmd_flag =
    let alt = if alt = "" then alt else "_" ^ alt in
    let cmd_flag = if cmd_flag="" then cmd_flag else "_" ^ cmd_flag in
    Format.sprintf "SMT_%s%s%s" prover alt cmd_flag
  in
  let sequent_is_valid = sequent_is_valid ~macro_axioms:true in
  if List.mem "constr" benchmarks then
    List.iter
      (fun (prover,alt) ->
            TraceSequent.register_query_alternative
              (bench_name prover alt "")
              (fun ~system:_ ~precise:_ s q ->
                  let s =
                    match q with
                    | None -> s
                    | Some q ->
                      let conclusion = Term.mk_ands q in
                      TraceSequent.set_conclusion conclusion s
                  in
                  sequent_is_valid
                    ~timeout:10
                    ~steps:None
                    ~provers:[prover,alt]
                    ~cmd_flag:""
                    ~poly:poly
                    ~hint_tables:[]
                    s))
      provers;
  if List.mem "autosimpl" benchmarks then
    List.iter
      (fun (prover,alt) ->
        List.iter (fun (cmd_flag) ->
            TraceTactics.AutoSimplBenchmark.register_alternative
              (bench_name prover alt cmd_flag)
              (fun s ->
                  sequent_is_valid
                    ~timeout:1
                    ~steps:None
                    ~provers:[prover,alt]
                    ~cmd_flag:cmd_flag
                    ~poly:poly
                    ~hint_tables:[]
                    s,
                  None);
            TraceTactics.AutoSimplBenchmark.register_alternative
              ("AutoSimpl")
              (fun s ->
                  match TraceTactics.simpl_direct
                      ~red_param:Reduction.rp_default
                      ~strong:true ~close:true s
                  with
                  | Ok [] -> true,None
                  | Error _ -> false,None
                  | Ok _ -> assert false)
      ) flags )
      provers;
  if List.mem "auto" benchmarks then
    List.iter
      (fun (prover,alt) ->
            TraceTactics.AutoBenchmark.register_alternative
              (bench_name prover alt "")
              (fun (_,s) ->
                    sequent_is_valid
                      ~timeout:10
                      ~steps:None
                      ~provers:[prover,alt]
                      ~cmd_flag:""
                      ~poly:poly
                      ~hint_tables:[]
                      s))
      provers

