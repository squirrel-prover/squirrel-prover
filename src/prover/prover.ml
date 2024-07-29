open Squirrelcore
open Ppenv

module L  = Location
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
  table         = TConfig.reset_params (Symbols.builtins_table ());
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

let do_set_option (st:state) (sp:Config.p_set_param) : state =
  { st with table = TConfig.set_param sp st.table }

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

let pp_goal fmt (ps:state) =
  match ps.current_goal, ps.subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf fmt "No subgoals remaining.@."
  | Some _, j :: _ ->
    Fmt.pf fmt "Focused goal (1/%d):@;%a@;@."
      (List.length ps.subgoals)
      Goal.pp j
  | _ -> assert false

let pp_subgoals fmt (ps:state) =
  match ps.current_goal, ps.subgoals with
  | None,[] -> assert false
  | Some _, [] -> Fmt.pf fmt "@[<v 0>[goal> No subgoals remaining.@]@."
  | Some _, subgoals ->
    List.iteri (fun i sg -> 
    Fmt.pf fmt "@[<v 0>[goal> (%d/%d):@;%a@;@]@." 
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
    Printer.prt `Goal "%a" pp_goal ps;
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
    Printer.prt `Goal "%a" pp_goal ps;
    ps
  | Some es, _ -> Command.cmd_error (StartProofError es)

(*---------------------    Goals handling  -----------------*)
let get_current_goal (ps:state) : ProverLib.pending_proof option = ps.current_goal

let get_system (ps:state) : SystemExpr.context option =
  match get_current_goal (ps) with
  | None -> None
  | Some (ProofObl g)
  | Some (UnprovedLemma (_, g)) -> Some (Goal.system g )

let add_new_goal_i
    (table : Symbols.table) (parsed_goal : Goal.Parsed.t) (ps : state) : state  
  =
  let name = match parsed_goal.Goal.Parsed.name with
    | None -> ProverLib.unnamed_goal ()
    | Some s -> s
  in
  if Symbols.Lemma.mem_s (Symbols.scope table) (L.unloc name) table then
    ProverLib.error (L.loc name) 
      "a goal or axiom with this name already exists";

  let parsed_goal = 
    { parsed_goal with Goal.Parsed.name = Some name } in
  let statement,goal = Goal.make table parsed_goal in
  let goals =  ProverLib.UnprovedLemma (statement,goal) :: ps.goals in
  { ps with goals }

let add_new_goal (ps:state)  
    (parsed_goal:Goal.Parsed.t L.located) : state =
  if ps.goals <> [] then
    ProverLib.error (L.loc parsed_goal) 
      "cannot add new goal: proof obligations remaining";

  let parsed_goal = L.unloc parsed_goal in
  add_new_goal_i ps.table parsed_goal ps

let first_goal (ps:state) : ProverLib.pending_proof =
  match ps.goals with
  | [] -> assert false
  | h :: _ -> h

let do_add_goal (st:state) (g:Goal.Parsed.t L.located) : state =
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
  let i, loc = L.unloc i_l, L.loc i_l in
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
      (L.{ pl_desc = "cycle"}, [TacticsArgs.Int_parsed i]) ->
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
    Printer.prt `Goal "%a" pp_goal st;
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
  if not (TConfig.interactive (get_table st)) then begin
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
  let cntxt = Typing.{ env; cntxt = InGoal; } in
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
    
    Symbols.Lemma.fold begin fun _ data acc -> 
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
    let t = fst (Typing.convert ~ty_env ~pat:true cntxt p) in
    find t
  | Global f ->
    let t = Typing.convert_global_formula ~ty_env ~pat:true cntxt f in
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

    Symbols.Lemma.fold (fun _ data acc -> 
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
        begin match get_system st with
          | Some s -> s.set
          | None -> Tactics.hard_failure (Failure "no default system");
        end
      | Some s -> SystemExpr.Parse.parse (get_table st) s
    end
  in
  SystemExpr.print_system (get_table st) system;

  if TConfig.print_trs_equations (get_table st)
  then
    Printer.prt `Result "@[<v>@;%a@;@]%!"
      Completion.print_init_trs 
      (get_table st)

(*------------------------------------------------------------------*)
let print_lemmas table (p:Symbols.p_path) : bool =
  let print1 (_path,data) =
    let data = Lemma.as_lemma data in
    Printer.prt `Default "%a@." Lemma.pp data;
  in
  try List.iter print1 (Symbols.Lemma.convert p table); true
  with Symbols.Error (_, Symbols.Unbound_identifier _) -> false 

(*------------------------------------------------------------------*)
let print_functions table (p : Symbols.p_path) : bool =
  let print1 (path,_) =
    let Symbols.OpData.{ ftype; def;} = Symbols.OpData.get_data path table in
    match def with
    | Concrete _ ->
      let data = Operator.get_concrete_data table path in
      Printer.prt `Default "%a@." Operator.pp_concrete_operator data

    | Abstract _ ->
      let data, _ = Symbols.OpData.get_abstract_data path table in
      Printer.prt `Default "fun %a : %a = %a@." 
        Symbols.OpData.pp_fname path
        Type.pp_ftype ftype 
        Symbols.OpData.pp_abstract_def data
  in
  try List.iter print1 (Symbols.Operator.convert p table); true
  with Symbols.Error (_, Symbols.Unbound_identifier _) -> false 

(*------------------------------------------------------------------*)
let print_names table (p:Symbols.p_path) : bool =
  let print1 (ls,_) =
    let fty = (Symbols.get_name_data ls table).n_fty in
    Printer.prt `Default "%s:%a@." 
      (Symbols.p_path_to_string p) Type.pp_ftype
      fty; 
  in
  try List.iter print1 (Symbols.Name.convert p table); true
  with Symbols.Error (_, Symbols.Unbound_identifier _) -> false 

(*------------------------------------------------------------------*)
let print_macros table (p:Symbols.p_path) : bool =
  let print1 (path,_data) =
    (* FIXME: do not print only global macros *)
    if Macros.is_global table path then 
      let macro = Symbols.Macro.get_data path table in
      Printer.prt `Default "%a@." Macros.pp (Macros.as_global_macro macro)
  in
  try List.iter print1 (Symbols.Macro.convert p table); true
  with Symbols.Error (_, Symbols.Unbound_identifier _) -> false 

(*------------------------------------------------------------------*)    
let print_games table (p:Symbols.p_path) : bool =
  let print1 (_, data) =
    let data = Crypto.data_as_game data in
    let ppe = default_ppe ~table ~dbg:false () in
    Printer.prt `Default "%a@." (Crypto._pp_game ppe) data
  in
  try List.iter print1 (Symbols.Game.convert p table); true
  with Symbols.Error (_, Symbols.Unbound_identifier _) -> false 

(*------------------------------------------------------------------*)
let do_print (st:state) (q:ProverLib.print_query) : unit =
    match q with
    | Pr_system s_opt -> print_system st s_opt
    | Pr_any l -> 
      begin
        let table = get_deepest_table st in
        let searchs_in = [
          print_lemmas;
          print_functions;
          print_names;
          print_games;
          print_macros; 
        ] in
        
        let found =
          List.fold_left 
            (fun found f -> found || f table l) 
            false
            searchs_in
        in

        if not found then
        Printer.prt `Default "%s not found@." (Symbols.p_path_to_string l)
      end

let do_eof (st:state) : state = 
    { st with prover_mode = AllDone }

exception Unfinished

(* Manage all commands. *)
let rec do_command 
    ?(driver_stack=[])
    ?(test=false) 
    ?(check=`Check) 
    (st:state) 
    (driver:Driver.t)
    (command:ProverLib.input) : state =
  let open ProverLib in
  let mode = get_mode st in
  Benchmark.set_position
    (let _,pos = Sedlexing.lexing_positions (Driver.get_lexbuf driver) in
     Format.asprintf
       "%s:%d:%s:%a"
       (Driver.name driver)
       pos.pos_lnum
       (Utils.odflt "_" (current_goal_name st))
       Bullets.pp st.bullets);
  match mode, command with
    | _, Reset -> init' ()
    | GoalMode, InputDescr decls -> do_decls st decls
    | _, Tactic t -> do_tactic ~check st (Driver.get_lexbuf driver) t
    | _, Print q  -> do_print st q; st
    | _, Search t -> do_search st t; st
    | _, Help ->
      Format.printf
        "See <https://squirrel-prover.github.io/documentation/>.@.";
      st
    | _, Prof ->
      Printer.prt `Dbg "%a" Prof.print ();
      st
    | WaitQed, Qed -> do_qed st
    | GoalMode, Hint h       -> add_hint st h
    | GoalMode, SetOption sp -> do_set_option st sp
    | GoalMode, Goal g       -> do_add_goal st g
    | GoalMode, Proof        -> do_start_proof ~check st
    | GoalMode, Include inc ->
      do_include ~dirname:(Driver.dirname driver) ~driver_stack st inc
    | GoalMode, EOF ->
      (* If interactive, never end. *)
      if TConfig.interactive (get_table st) then st else do_eof st
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
      ?(test=true) ?(driver_stack=[]) (st:state) ~dirname (i:ProverLib.include_param)
    : state
=
  let load_paths = Driver.mk_load_paths dirname in
  let driver =
    Driver.from_include driver_stack load_paths i.th_name
  in
  let interactive = TConfig.interactive (get_table st) in
  let checkInclude = 
    if TConfig.checkInclude (get_table st) then `Check 
    else begin
      if List.exists 
          (fun x -> L.unloc x = "admit") i.ProverLib.params 
      then `NoCheck
      else `Check
    end in
  let new_driver_stack = driver :: driver_stack in
  let st = 
    try 
      let st = 
        do_all_commands_in
          ~driver_stack:new_driver_stack ~check:checkInclude ~test st driver
      in
      (* Adding imported file in the symbol table. *)
      let table, _ =
        let name = match i.th_name with Name s -> s | Path s -> s in
        Symbols.Import.declare ~approx:false st.table name in
      { st with table }

    with e when Errors.is_toplevel_error ~interactive:interactive ~test e ->
      let err_mess fmt =
        Fmt.pf fmt "@[<v 0>Include %S failed:@;@[%a@]@]"
          (L.unloc (ProverLib.lsymb_of_load_path i.th_name))
          (Errors.pp_toplevel_error ~interactive:interactive ~test driver) e
      in
      Driver.close driver;
      Command.cmd_error (IncludeFailed err_mess)
  in
  Driver.close driver;
  Printer.prt `Warning "Loaded \"%s.sp\"." (Driver.name driver);
  st

and do_all_commands_in ?(driver_stack=[])
    ~check ~test (st:state) (driver:Driver.t) : state
  =
  let interactive = TConfig.interactive (get_table st) in
  match Driver.next_input ~test ~interactive driver (get_mode st) with
  | EOF ->
      (* ↓ If test or interactive, never end ↓ *)
      if test || interactive 
      then st else do_eof st
  | cmd ->
     do_all_commands_in ~driver_stack ~check ~test
       (do_command ~driver_stack ~test ~check st driver cmd) driver

and exec_command 
    ?(check=`Check) ?(test=false) (s:string) (st:state) : state  = 
  let interactive = TConfig.interactive (get_table st) in
  let input =
    Driver.next_input
      ~test ~interactive (Driver.from_string s) (get_mode st) in
  do_command ~test ~check st (Driver.from_string s) input

(** Execute all commands from a string. *)
let exec_all ?(check=`Check) ?(test=false) (st:state) (s:string) =
  let driver = Driver.from_string s in
  do_all_commands_in ~check ~test st driver

let init : ?with_prelude:bool -> unit -> state =
  (* Memoise state with prelude. *)
  let state0 : state option ref = ref None in
  fun ?(with_prelude=true) () : state ->
    match !state0 with
    | Some st when with_prelude = true -> st
    | _ -> 
      let state = init' () in
      if with_prelude then begin
        let inc =
          ProverLib.{ th_name =
                        Name (L.mk_loc L._dummy "Prelude");
                      params = []; }
        in
        (* process the prelude file *)
        let state = do_include ~dirname:Driver.theory_dir state inc in
        (* define the macros defining the builtin execution models *)
        let table = Macros.define_execution_models state.table in
        let () = Symbols.set_builtins_table_after_processing_prelude table in
        let state = { state with table } in
        state0 := Some state;
        state
      end
      else state

(* Run entire Squirrel file with given path as string. *)
let run ?(test=false) (file_path:string) : unit =
  match Driver.from_file file_path with
  | Ok driver ->
    let _ : state =
      do_all_commands_in
        ~driver_stack:[driver] ~test ~check:`Check (init ()) driver
    in ()
  | Error _ -> failwith "File not found!"
