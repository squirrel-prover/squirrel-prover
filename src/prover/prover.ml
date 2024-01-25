open Squirrelcore
module Sv = Vars.Sv

(*------------------ Prover ----------------------------------*)
(** {2 Prover state}
    The term "goal" refers to two things below:

    - A toplevel lemma declaration
      which is represented (with some redundancy) by a [Goal.statement]
      and a [Goal.t] which is the associated sequent that has to be
      proved, i.e. the root of the required proof tree.

    - A sequent that has to be proved (i.e. a node in a proof tree)
      which is represented by a [Goal.t].

    For now we use the adjectives toplevel and inner to distinguish
    the two kinds of goals. *)
type state = {
  goals        : ProverLib.pending_proof list;
  table        : Symbols.table; 
  current_goal : ProverLib.pending_proof option;
  subgoals     : Goal.t list;
  bullets      : Bullets.path;
  prover_mode  : ProverLib.prover_mode;
}

(* GoalMode is always the initial prover_mode *)
let init' () : state = 
{ goals         = [];
  table         = TConfig.reset_params Symbols.builtins_table;
  current_goal  = None;
  bullets       = Bullets.empty_path;
  subgoals      = [];
  prover_mode   = ProverLib.GoalMode;
}

let get_table (ps:state) : Symbols.table =
  ps.table

let get_mode (ps:state) : ProverLib.prover_mode =
  ps.prover_mode

let get_subgoals (ps:state) : Goal.t list =
  ps.subgoals

let set_table (ps:state) (table: Symbols.table) : state =
  { ps with table }

let set_param (ps:state) (sp: Config.p_set_param) : state =
  { ps with table = TConfig.set_param sp ps.table }

let do_set_option (st:state) (sp:Config.p_set_param) : state =
  set_param st sp

let add_hint (ps:state) (h: Hint.p_hint) : state =
  let table = 
    match h with
    | Hint.Hint_rewrite id -> 
        ProcessDecl.add_hint_rewrite ps.table id ps.table
    | Hint.Hint_smt     id -> 
        ProcessDecl.add_hint_smt     ps.table id ps.table
  in
  { ps with table; }

let abort (ps:state) : state = 
  { ps with current_goal  = None; 
            bullets       = Bullets.empty_path;
            subgoals      = [];
            prover_mode   = ProverLib.GoalMode;
  }

let is_proof_completed (ps:state) : bool =
  ps.subgoals = [] && Bullets.is_empty ps.bullets

let current_goal_name (ps:state) : string option =
  Utils.omap (function 
      | ProverLib.UnprovedLemma (stmt,_) -> stmt.Goal.name
      | ProofObl _ -> "proof obligation" ) ps.current_goal

(*--------------------- Printings         ------------------*)
let str_mode = function
  | ProverLib.GoalMode -> "GoalMode"
  | ProverLib.ProofMode -> "ProofMode"
  | ProverLib.WaitQed -> "WaitQed"
  | ProverLib.AllDone -> "AllDone"

let pp_goal (ps:state) ppf () = match ps.current_goal, ps.subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "No subgoals remaining.@."
  | Some _, j :: _ ->
    Fmt.pf ppf "Focused goal (1/%d):@;%a@;@."
      (List.length ps.subgoals)
      Goal.pp j
  | _ -> assert false

let pp_subgoals (ps:state) ppf () = match ps.current_goal, ps.subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf ppf "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, subgoals ->
    List.iteri (fun i sg -> 
    Fmt.pf ppf "@[<v 0>[goal> (%d/%d):@;%a@;@]@." 
      (i+1) 
      (List.length subgoals) 
      Goal.pp sg
    ) subgoals
  | _ -> assert false

let try_complete_proof (ps:state) : state =
  if is_proof_completed ps then begin
    Printer.prt `Goal "lemma %s is proved@."
      (Utils.oget (current_goal_name ps));
    { ps with prover_mode = WaitQed }
  end
  else begin
    Printer.prt `Goal "%a" (pp_goal ps) ();
    { ps with prover_mode = ProofMode}
  end

let complete_proof (ps:state) : state = 
  assert (is_proof_completed ps);

  if ps.current_goal = None then
    Tactics.hard_failure
      (Tactics.Failure "cannot complete proof: no current goal");

  let table = match Utils.oget ps.current_goal with
    | ProofObl _ -> ps.table
    | UnprovedLemma (gc, _) -> Lemma.add_lemma `Lemma gc ps.table
  in
  { ps with current_goal = None;
            bullets = Bullets.empty_path;
            subgoals = [];
            table = table;
            prover_mode = ProverLib.GoalMode
  }

let do_qed (st : state) : state =
  let prover_state = complete_proof st in
  Printer.prt `Result "Exiting proof mode.@.";
  prover_state

let start_proof (ps:state) (check : [`NoCheck | `Check])
  : (string option * state) = 
  match ps.current_goal, ps.goals with
  | None, pending_proof :: remaining_goals ->
    assert (ps.subgoals = []);

    let goals = remaining_goals in

    let goal = match pending_proof with
      | ProofObl goal
      | UnprovedLemma (_,goal) -> goal
    in
    let current_goal = Some pending_proof in

    let subgoals, bullets, mode = begin 
      match check with
      | `Check -> [goal], Bullets.initial_path, ProverLib.ProofMode
      | `NoCheck -> [], Bullets.empty_path, ProverLib.WaitQed
    end in
      (None, { ps with goals; subgoals; bullets; current_goal;
                            prover_mode = mode })
  | Some _,_ ->
    (Some "Cannot start a new proof (current proof is not done).",
     ps)

  | _, [] ->
    (Some "Cannot start a new proof (no goal remaining to prove).",
     ps)

let do_start_proof ?(check=`NoCheck) (st: state) : state =
  match start_proof st check with
  | None, ps ->
    Printer.prt `Goal "%a" (pp_goal ps) ();
    ps
  | Some es, _ -> Command.cmd_error (StartProofError es)

(*---------------------    Goals handling  -----------------*)
let get_current_goal (ps:state) : ProverLib.pending_proof option = ps.current_goal

let get_current_system (ps:state) : SystemExpr.context option =
  match get_current_goal (ps) with
  | None -> None
  | Some (ProofObl g)
  | Some (UnprovedLemma (_, g)) -> Some (Goal.system g )

let add_new_goal_i (table:Symbols.table) (parsed_goal:Goal.Parsed.t) 
    (ps:state) : state  =
  let name = match parsed_goal.Goal.Parsed.name with
    | None -> ProverLib.unnamed_goal ()
    | Some s -> s
  in
  if Lemma.mem name table then
    ProverLib.error (Location.loc name) 
      "a goal or axiom with this name already exists";

  let parsed_goal = 
    { parsed_goal with Goal.Parsed.name = Some name } in
  let statement,goal = Goal.make table parsed_goal in
  let goals =  ProverLib.UnprovedLemma (statement,goal) :: ps.goals in
  { ps with goals }

let add_new_goal (ps:state)  
    (parsed_goal:Goal.Parsed.t Location.located) : state =
  if ps.goals <> [] then
    ProverLib.error (Location.loc parsed_goal) 
      "cannot add new goal: proof obligations remaining";

  let parsed_goal = Location.unloc parsed_goal in
  add_new_goal_i ps.table parsed_goal ps

let first_goal (ps:state) : ProverLib.pending_proof =
  match ps.goals with
  | [] -> assert false
  | h :: _ -> h

let do_add_goal (st:state) (g:Goal.Parsed.t Location.located) : state =
  let new_ps = add_new_goal st g in
  (* for printing new goal ↓ *)
  let goal,name = match first_goal new_ps with
    | ProverLib.UnprovedLemma (stmt,g) -> g, stmt.Goal.name
    | _ -> assert false (* should be only ↑ *)
  in
  Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." name Goal.pp_init goal;
  (* return toplevel state with new prover_state *)
  new_ps

let add_proof_obl (goal : Goal.t) (ps:state) : state = 
  let goals =  ProverLib.ProofObl (goal) :: ps.goals in
  { ps with goals }

let add_decls (st:state) (decls : Decl.declarations) 
  : state * Goal.t list =
  let table, proof_obls = ProcessDecl.declare_list 
      (get_table st) decls in
  let ps : state = List.fold_left (fun ps goal ->
      add_proof_obl goal ps) st proof_obls in
  let ps = set_table ps table in
  { ps with prover_mode = ProverLib.GoalMode }, proof_obls

let do_decls (st:state) (decls : Decl.declarations) : state =
  let new_prover_state, proof_obls = 
    add_decls st decls in
  if proof_obls <> [] then
    Printer.pr "@[<v 2>proof obligations:@;%a@]"
      (Fmt.list ~sep:Fmt.cut Goal.pp_init) proof_obls;
  new_prover_state

let get_first_subgoal (ps:state) : Goal.t =
  match ps.current_goal, ps.subgoals with
  | Some _, j :: _ -> j
  | _ -> raise Not_found

let get_deepest_table (st:state) : Symbols.table = 
  begin match st.prover_mode with
  | ProofMode -> 
    let goal = get_first_subgoal st
    in
    begin match goal with
      | Goal.Local  j -> (LowTraceSequent.env j).table
      | Goal.Global j -> (LowEquivSequent.env j).table
    end
  | _ -> get_table st
  end

(*--------------------- Tactics evaluation -----------------*)
(** [eval_tactic_focus tac] applies [tac] to the focused goal. *)
let eval_tactic_focus (tac:ProverTactics.AST.t) (ps:state) : state = 
  match ps.subgoals with
  | [] -> assert false
  | judge :: ejs' ->
    if not (Bullets.tactic_allowed ps.bullets) then
      Tactics.hard_failure (Failure "bullet needed before tactic");
    
    let post_quantum = TConfig.post_quantum (ps.table) in
    let new_j = ProverTactics.AST.eval_judgment ~post_quantum tac judge in
    begin
      try
        let bullets = Bullets.expand_goal (List.length new_j)
            ps.bullets  in
        {
          ps with subgoals = new_j @ ejs'; bullets = bullets
        }
      with Bullets.Error _ -> Tactics.(hard_failure (Failure "bullet error"))
    end

let cycle i_l l =
  let i, loc = Location.unloc i_l, Location.loc i_l in
  let rec cyc acc i = function
    | [] -> Tactics.hard_failure ~loc (Tactics.Failure "cycle error")
    | a :: l ->
      if i = 1 then l @ (List.rev (a :: acc))
      else cyc (a :: acc) (i - 1) l in
  if i = 0 then l else
  if i < 0 then cyc [] (List.length l + i) l
  else cyc [] i l

let eval_tactic (utac:ProverTactics.AST.t) (ps:state) : state =
  match utac with
  | Tactics.Abstract
      (Location.{ pl_desc = "cycle"}, [TacticsArgs.Int_parsed i]) ->
    (* TODO do something more for bullets?
       Cycling the list of subgoals does not change its length so
       nothing will break (fail) wrt bullets, but the result will
       be meaningless: we may want to warn the user, forbid cycles
       accross opened bullets, or even update the Bullets.path to
       reflect cycles. *)
    { ps with subgoals = cycle i ps.subgoals }
  | _ -> eval_tactic_focus utac ps

(*----------------------- Bullets --------------------------*)
(** Insert a bullet in the proof script. *)
let open_bullet (ps:state) (bullet : string) : state =
  assert (bullet <> "");
  try { ps with bullets = Bullets.open_bullet bullet ps.bullets } with
  | Bullets.Error _ -> Tactics.(hard_failure (Failure "invalid bullet"))

let invalid_brace () =
  Tactics.hard_failure (Failure "invalid brace")

(** Open a brace in the proof script. *)
let open_brace (ps:state) : state =
  try { ps with bullets = Bullets.open_brace ps.bullets } with
  | Bullets.Error _ -> invalid_brace ()

(** Close a brace in the proof script. *)
let close_brace (ps:state) : state =
  try { ps with bullets = Bullets.close_brace ps.bullets } with
  | Bullets.Error _ -> invalid_brace ()

let tactic_handle (ps:state) = function
 | ProverLib.Bullet bl    -> open_bullet ps bl
 | ProverLib.Brace `Open  -> open_brace ps
 | ProverLib.Brace `Close -> close_brace ps
 | ProverLib.BTactic utac  -> eval_tactic utac ps

(*---------------- do_* commands handling ------------------*)
let do_print_goal (st:state) : unit = 
  match get_mode st with
  | ProverLib.ProofMode -> 
    Printer.prt `Goal "%a" (pp_goal st) ();
  | _ -> ()

let do_tactic' ?(check=`Check) (state : state) (l:ProverLib.bulleted_tactics) : state =
  begin match check with
    | `NoCheck -> assert (state.prover_mode = WaitQed)
    | `Check   -> 
      if state.prover_mode <> ProverLib.ProofMode then
        Command.cmd_error UnexpectedCommand;
  end;

  match check with
  | `NoCheck -> state
  | `Check   ->
    let state = 
      begin 
        try List.fold_left tactic_handle state l
        with
          | e -> 
            raise e
      end in
    try_complete_proof state

let do_tactic ?(check=`Check) (st : state) (lex:Sedlexing.lexbuf)
    (l:ProverLib.bulleted_tactics) : state =
  if not (TConfig.interactive (get_table st)) then 
    begin
      let (_, curr_p) = Sedlexing.lexing_positions lex in
      let lnum = curr_p.pos_lnum in
    let b_tacs = List.filter_map 
      (function ProverLib.BTactic t -> Some t | _ -> None) l
    in
    match b_tacs with
      | [utac] ->
          Printer.prt `Prompt "Line %d: %a" lnum ProverTactics.AST.pp utac
      | _ ->
          Printer.prt `Prompt "Line %d: ??" lnum
  end;
    do_tactic' ~check st l

(*----------------------- Search --------------------------*)
let search_about (st:state) (q:ProverLib.search_query) : 
  (Lemma.lemma * Equiv.any_form list) list =
  let env = 
    begin match st.prover_mode with
    | ProofMode -> 
      let goal = get_first_subgoal st
      in
      begin match goal with
        | Goal.Local  j -> LowTraceSequent.env j
        | Goal.Global j -> LowEquivSequent.env j
      end
    | _ -> 
      begin match q with 
      | ProverLib.Srch_inSys (_,sysexpr) ->
          let set = SystemExpr.Parse.parse 
                            (get_table st) sysexpr in
          let system: SystemExpr.context option = 
            Some ({ set  = set;
                    pair = Some (SystemExpr.to_pair set)
                  }) in
          Env.init ~table:st.table ?system () 
      | _ -> Env.init ~table:st.table ()
      end
    end
  in
  Printer.prt `Default "@[<2>Search in context system@ [@[%a@]].@]@."
    SystemExpr.pp env.system.set;

  let t = match q with
    | ProverLib.Srch_inSys (t,_)
    | ProverLib.Srch_term t -> t in
  let cntxt = Theory.{ env; cntxt = InGoal; } in
  let ty_env = Type.Infer.mk_env () in

  let find (t:Term.term) =
    let pat_op_vars =
      Vars.Tag.local_vars ~const:true
        (Sv.elements (Vars.Sv.filter Vars.is_pat (Term.fv t)))
    in
    let pat = Term.{
        pat_op_tyvars = [];
        pat_op_vars;
        pat_op_term = t; } 
    in

    (* allow capture of bound variables when matching *)
    let option = { Match.default_match_option with allow_capture = true; } in
    
    Symbols.Lemma.fold begin fun _ _ data acc -> 
        let g = Lemma.as_lemma data in
        let sys = g.stmt.system in 
        let res = begin match g.stmt.formula with
        | Global f -> Match.E.find ~option env.table sys pat f
        | Local  f -> Match.T.find ~option env.table sys pat f
        end in
        begin match res with
          | [] -> acc
          | _ -> 
            let any_res = 
              List.map (fun x -> Equiv.Local x) res in
            (g,any_res)::acc
        end
    end [] env.table in

  match t with
  | Local p -> 
    let t = fst (Theory.convert ~ty_env ~pat:true cntxt p) in
    find t
  | Global f ->
    let t = Theory.convert_global_formula ~ty_env ~pat:true cntxt f in
    let pat_op_vars =
      Vars.Tag.local_vars ~const:true
        (Sv.elements (Sv.filter Vars.is_pat (Equiv.fv t)))
    in
    let pat = Term.{
        pat_op_tyvars = [];
        pat_op_vars;
        pat_op_term = t; } in

    (* allow capture of bound variables when matching *)
    let option = { Match.default_match_option with allow_capture = true; } in

    Symbols.Lemma.fold (fun _ _ data acc -> 
        let g = Lemma.as_lemma data in
        let sys = g.stmt.system in 
        let res = begin match g.stmt.formula with
        | Global f -> Match.E.find_glob ~option env.table sys pat f
        | Local  _ -> [] (* can't find Equiv.form in
                                      Term.term ? *)
        end in
        begin match res with
        | [] -> acc
        | _ ->
          let any_res = 
            List.map (fun x -> Equiv.Global x) res in
          (g,any_res)::acc
        end
      ) [] env.table

let do_search (st:state) (t:ProverLib.search_query) : unit =
  let matches = search_about st t in
  Printer.prt `Default "Search result(s):@.@.";
  let print_all fmt matches =
  List.iter (fun (lemma,_:Lemma.lemma * Equiv.any_form list) -> 
        Fmt.pf fmt "%a@.@."
          Lemma.pp lemma
    ) matches in
  Printer.prt `Default "%a" print_all matches

let print_system (st:state) (s_opt:SystemExpr.Parse.t option) 
  : unit =
  let system = 
    begin match s_opt with
      | None   -> 
        begin match get_current_system st with
          | Some s -> s.set
          | None -> Tactics.hard_failure 
                      (Failure "no default system");
        end
      | Some s -> SystemExpr.Parse.parse 
                    (get_table st) s
    end
  in
  SystemExpr.print_system 
    (get_table st) system;

  if TConfig.print_trs_equations 
      (get_table st)
  then
    Printer.prt `Result "@[<v>@;%a@;@]%!"
      Completion.print_init_trs 
      (get_table st)

let print_lemma table (l:Theory.lsymb) : bool = 
  try
    let lem = Lemma.find l table in
    Printer.prt `Default "%a@." Lemma.pp lem;
    true
  with _ -> false

let print_function table (l:Theory.lsymb) : bool =
  try
    let f = Symbols.Function.of_lsymb l table in
    let ftype, fdef = Symbols.Function.get_def f table in
    let _ = 
      begin match fdef with
        | Symbols.Operator -> 
          let func = Symbols.Function.get_data f table in
          begin match func with
            | Operator.Operator op ->
              Printer.prt `Default "%a@." Operator.pp_operator op
            | _ -> assert false
          end
        | func_def -> 
          Printer.prt `Default "fun %s : %a : %a@." 
            (Location.unloc l)
            Type.pp_ftype ftype 
            Symbols.pp_function_def func_def 
      end in
    true
  with _ -> false

let print_name table (l:Theory.lsymb) : bool =
  try
    let fty = (Symbols.Name.def_of_lsymb l table).n_fty in
    Printer.prt `Default "%s:%a@." (Location.unloc l) Type.pp_ftype
      fty; 
    true
  with _ -> false

let print_macro table (l:Theory.lsymb) : bool =
  try
    let m = (Symbols.Macro.of_lsymb l table) in
    let macro = Symbols.Macro.get_data m table in
    Printer.prt `Default "%a@." Macros.pp (Macros.as_macro macro);
    true
  with _ -> false

let print_game table (l:Theory.lsymb) : bool =
  try
    let g = Crypto.find table l in
    Printer.prt `Default "%a@." Crypto.pp_game g; 
    true
  with _ -> false

let do_print (st:state) (q:ProverLib.print_query) : unit =
    match q with
    | Pr_system s_opt -> print_system st s_opt
    | Pr_any l -> 
      begin
        let table = (get_deepest_table st) in
        let searchs_in = [
          print_lemma;    (* first try printing lemma *)
          print_function; (* then try printing function *)
          print_name;     (* then try printing name *)
          print_game;     (* then try printing games *)
          print_macro;    (* FIXME then try printing macro *)
        ] in
        
        let found = List.fold_left 
            (fun found f -> found || f table l) 
            false
            searchs_in in

        if not found then
        Printer.prt `Default "%s not found@." (Location.unloc l)
      end

let do_eof (st:state) : state = 
    { st with prover_mode = AllDone }

exception Unfinished

(* Manage all commands. *)
let rec do_command 
    ?(main_mode=`Stdin) 
    ?(file_stack=[]) 
    ?(test=false) 
    ?(check=`Check) 
    (st:state) 
    (file:Driver.file) 
    (command:ProverLib.input) : state =
  let open ProverLib in
  let pst = st in
  let mode = get_mode st in
  TraceSequent.Benchmark.set_position
    (let _,pos = Sedlexing.lexing_positions file.f_lexbuf in
     Format.sprintf
       "%s:%d"
       (match file.f_path with
        | `File s -> s | `Stdin -> "stdin" | `Str -> "str")
       pos.pos_lnum);
  match mode, command with
    | _, Reset                   -> init' ()
    | GoalMode, InputDescr decls -> do_decls st decls
    | _, Tactic t                -> do_tactic ~check st file.f_lexbuf t
    | _, Print q                 -> do_print pst q; st
    | _, Search t                -> do_search pst t; st
    | _, Help ->
      Format.printf
        "See <https://squirrel-prover.github.io/documentation/>.@.";
      st
    | _, Prof ->
      Printer.prt `Dbg "%a" Prof.print ();
      st
    | WaitQed, Qed               -> do_qed st
    | GoalMode, Hint h           -> add_hint st h
    | GoalMode, SetOption sp     -> set_param st sp
    | GoalMode, Goal g           -> do_add_goal st g
    | GoalMode, Proof            -> do_start_proof ~check st
    | GoalMode, Include inc      -> do_include ~main_mode ~file_stack st inc
    | GoalMode, EOF              -> 
      (* ↓ If interactive, never end ↓ *)
      if TConfig.interactive (get_table st) 
      then st else do_eof st
    | WaitQed, Abort -> 
      if test then
        raise (Failure "Trying to abort a completed proof.");
      Command.cmd_error AbortIncompleteProof
    | ProofMode, Abort ->
      Printer.prt `Result
        "Exiting proof mode and aborting current proof.@.";
      abort st
    | _, Qed ->
      if test then raise Unfinished;
      Command.cmd_error UnexpectedCommand
    | _, _ -> 
      Printer.pr "Unexpected command while in mode %s." (str_mode mode);
      Command.cmd_error UnexpectedCommand

and do_include
      ?(test=true) ?(main_mode=`Stdin) ?(file_stack=[]) (st:state) (i:ProverLib.include_param)
    : state
=
  (* if main_mode = `Stdin will add cwd in path with theories *)
  let load_paths = Driver.mk_load_paths ~main_mode () in
  let file =
    Driver.include_get_file file_stack load_paths i.th_name
  in
  let interactive = TConfig.interactive (get_table st) in
  let checkInclude = 
    if TConfig.checkInclude (get_table st) then `Check 
    else begin
      if List.exists 
          (fun x -> Location.unloc x = "admit") i.ProverLib.params 
      then `NoCheck
      else `Check
    end in
  let new_file_stack = file :: file_stack in
  let st = 
    try 
      let st = 
        do_all_commands_in
          ~main_mode ~file_stack:new_file_stack ~check:checkInclude ~test st file 
      in

      (*Adding the file as included library in table theories' symbols *)
      let table, _ = 
        let name = match i.th_name with Name s -> s | Path s -> s in
        Symbols.Theory.declare_exact st.table name () in
      { st with table }

    with e when Errors.is_toplevel_error ~interactive:interactive ~test e ->
      let err_mess fmt =
        Fmt.pf fmt "@[<v 0>Include %S failed:@;@[%a@]@]"
          (Location.unloc (ProverLib.lsymb_of_load_path i.th_name))
          (Errors.pp_toplevel_error ~interactive:interactive ~test file) e
      in
      Driver.close_chan file.f_chan;
      Command.cmd_error (IncludeFailed err_mess)
  in
  Driver.close_chan file.f_chan;
  Printer.prt `Warning "Loaded \"%s.sp\"." file.f_name;
  st

and do_all_commands_in ~main_mode ?(file_stack=[]) 
    ~check ~test (st:state) (file:Driver.file) : state 
  =
  let interactive = TConfig.interactive (get_table st) in
  match Driver.FromFile.next_input ~test ~interactive file (get_mode st) with
  | EOF ->
      (* ↓ If test or interactive, never end ↓ *)
      if test || interactive 
      then st else do_eof st
  | cmd ->
     do_all_commands_in ~main_mode ~file_stack ~check ~test
       (do_command ~main_mode ~file_stack ~test ~check st file cmd) file

and exec_command 
    ?(check=`Check) ?(test=false) (s:string) (st:state) : state  = 
  let interactive = TConfig.interactive (get_table st) in
  let input =
    Driver.FromFile.next_input
      ~test ~interactive (Driver.file_from_str s) (get_mode st) in
  do_command ~test ~check st (Driver.file_from_str s) input

and exec_all ?(check=`Check) ?(test=false) (st:state) (s:string) = 
  let file_from_string = Driver.file_from_str s in
  do_all_commands_in ~main_mode:`Stdin ~check ~test st file_from_string 

let init : ?withPrelude:bool -> unit -> state =
  (* memoise state with prelude *)
  let state0 : state option ref = ref None in
  
  fun ?(withPrelude=true) () : state ->
    match !state0 with
    | Some st when withPrelude = true -> st
    | _ -> 
      let state = init' () in
      if withPrelude then begin
        let inc =
          ProverLib.{ th_name = Name (Location.mk_loc Location._dummy
                          "Prelude");
                      params = []; }
        in
        let state = do_include ~main_mode:(`File "Prelude") state inc in
        state0 := Some state;
        state
      end
      else state

(* run entire squirrel file with given path as string *)
let run ?(test=false) (file_path:string) : unit =
  match Driver.file_from_path LP_none 
          (Filename.remove_extension file_path) with
  | Some file ->
    let name = Filename.remove_extension file.f_name in
    let _ : state =
      do_all_commands_in ~main_mode:(`File name) ~file_stack:[file] ~test ~check:`Check (init ()) file
    in ()
  | None -> failwith "File not found !" 
