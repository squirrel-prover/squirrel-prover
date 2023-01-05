open Utils
open Driver

module L = Location

module Initialization = struct
  (* Opening these modules is only useful for their side effects,
   * e.g. registering tactics - hence the use of "open!" *)
  open! LowTactics
  open! TraceTactics
  open! EquivTactics
  open! HighTactics
end

let usage = Fmt.str "Usage: %s filename" (Filename.basename Sys.argv.(0))

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

(** check if an exception is handled *)
let is_toplevel_error ~test (e : exn) : bool =
  match e with
  | Parserbuf.Error                 _
  | ProverLib.Error                 _
  | Command.Cmd_error                       _
  | Process.Error                   _
  | ProcessDecl.Error               _
  | Theory.Conv                     _
  | Symbols.Error                   _
  | System.Error                    _
  | SystemExpr.Error                _
  | Tactics.Tactic_soft_failure     _
  | Tactics.Tactic_hard_failure     _ -> not test

  | _e when !interactive -> not test

  | _ -> false

(** [is_toplevel_error] must be synchronized with [pp_toplevel_error] *)
let pp_toplevel_error
    ~test
    (state : driver_state)
    (fmt : Format.formatter)
    (e : exn) : unit
  =
  let pp_loc_error     = pp_loc_error     state in
  let pp_loc_error_opt = pp_loc_error_opt state in

  match e with
  | Parserbuf.Error s ->
    Fmt.string fmt s

  | ProverLib.Error e ->
    ProverLib.pp_error pp_loc_error fmt e

  | Command.Cmd_error e ->
    Command.pp_cmd_error fmt e

  | Process.Error e ->
    (Process.pp_error pp_loc_error) fmt e

  | ProcessDecl.Error e when not test ->
    (ProcessDecl.pp_error pp_loc_error) fmt e

  | Theory.Conv e when not test ->
    (Theory.pp_error pp_loc_error) fmt e

  | Symbols.Error e when not test ->
    (Symbols.pp_error pp_loc_error) fmt e

  | System.Error e when not test ->
    Format.fprintf fmt "System error: %a" System.pp_error e

  | SystemExpr.Error e when not test ->
    Format.fprintf fmt "System error: %a" SystemExpr.pp_error e

  | Tactics.Tactic_soft_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic failed: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | Tactics.Tactic_hard_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic ill-formed or unapplicable: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | e when !interactive ->
    Fmt.pf fmt "Anomaly, please report: %s" (Printexc.to_string e)
    
  | _ -> assert false

(*------------------------------------------------------------------*)

exception Unfinished

(*---------------- Main --------------------------------------------*)
let do_undo (state : driver_state) (nb_undo : int) : driver_state =
  let history_state, toplvl_state =
  HistoryTP.reset_state state.history_state nb_undo in
  let () = match ToplevelProver.get_mode toplvl_state with
    | ProofMode -> Printer.pr "%a" (ToplevelProver.pp_goal
                     toplvl_state) ()
    | GoalMode -> Printer.pr "%a" Action.pp_actions
                    (ToplevelProver.get_table toplvl_state)
    | WaitQed -> ()
    | AllDone -> assert false in
  { state with toplvl_state; history_state; }

let do_decls (state : driver_state) (decls : Decl.declarations) :
  driver_state =
  let toplvl_state = ToplevelProver.do_decls
    state.toplvl_state decls in
  { state with toplvl_state; }

let do_print (state : driver_state) (q : ProverLib.print_query) 
  : driver_state =
  ToplevelProver.do_print state.toplvl_state q;
  state

let do_search (state : driver_state) (t : ProverLib.search_query) 
  : driver_state =
  ToplevelProver.do_search state.toplvl_state t;
  state

(*----------Part can be done here and tactic handling in Prover ----*)
let do_tactic (state : driver_state) (l:ProverLib.bulleted_tactics) : driver_state =
  begin match state.check_mode with
    | `NoCheck -> assert (ToplevelProver.get_mode state.toplvl_state = WaitQed)
    | `Check   -> 
      if ToplevelProver.get_mode state.toplvl_state <> ProverLib.ProofMode then
        Command.cmd_error Unexpected_command;
  end;

  if not !interactive then 
  begin
    let lnum = state.file.f_lexbuf.lex_curr_p.pos_lnum in
    let b_tacs = List.filter_map 
      (function ProverLib.BTactic t -> Some t | _ -> None) l
    in
    match b_tacs with
      | [utac] ->
          Printer.prt `Prompt "Line %d: %a" lnum ProverTactics.pp_ast utac
      | _ ->
          Printer.prt `Prompt "Line %d: ??" lnum
  end;

  match state.check_mode with
  | `NoCheck -> state
  | `Check   ->
    let saved_ps = state.toplvl_state in
    let toplvl_state = 
      begin 
        try List.fold_left 
              ToplevelProver.tactic_handle state.toplvl_state l
        with
          | e -> 
            (* XXX ↓ impure ↓  XXX will only reset Config params refs *)
            ignore (HistoryTP.reset_from_state 
                      saved_ps) ; raise e
      end in
    let toplvl_state = 
      ToplevelProver.try_complete_proof toplvl_state
    in { state with toplvl_state }

let do_qed (state : driver_state) : driver_state =
  let toplvl_state = ToplevelProver.do_qed
      state.toplvl_state in
  { state with toplvl_state }

let do_add_hint (state : driver_state) (h : Hint.p_hint) : driver_state =
  { state with toplvl_state = ToplevelProver.do_add_hint
                   state.toplvl_state h; }

(* XXX Touch global Config that has to be recorded in History *)
let do_set_option (state : driver_state) (sp : Config.p_set_param) :
  driver_state =
  match Config.set_param sp with
  | `Failed _ -> (* TODO should be only ↓ *)
    { state with toplvl_state = ToplevelProver.do_set_option
                state.toplvl_state sp; }
  | `Success -> state

let do_add_goal 
    (state : driver_state)
    (g : Goal.Parsed.t Location.located) 
  : driver_state 
  =
  let toplvl_state = ToplevelProver.do_add_goal 
      state.toplvl_state g in
  { state with toplvl_state }

let do_start_proof (state : driver_state) : driver_state =
  { state with 
    toplvl_state = ToplevelProver.do_start_proof
      state.toplvl_state state.check_mode }

let do_eof (state : driver_state) : driver_state =
  assert (state.file_stack = []);
  { state with toplvl_state = 
                 ToplevelProver.do_eof state.toplvl_state }

let rec do_include 
    ~test
    (state : driver_state)
    (i : ProverLib.include_param) 
  : driver_state 
  =
  let file = include_get_file state i.th_name in
  let file_stack = state.file :: state.file_stack in

  let hstate = { state with 
     history_state = HistoryTP.push_pt_history state.history_state }
  in

  let check_mode = 
    if List.exists (fun x -> L.unloc x = "admit") i.ProverLib.params 
    then `NoCheck
    else `Check
  in
  let incl_state = { hstate with file; file_stack; check_mode; } in

  (* try to do the include *)
  try
    let final_state = do_all_commands ~test incl_state in
    Printer.prt `Warning "loaded: %s.sp" final_state.file.f_name;

    { state with toplvl_state = final_state.toplvl_state }

    (* XXX Does that mean that file, file_stack and check_mode are the
     * only values that are relevant in driver_state → do_include ? *)

  (* include failed, revert state *)
  (* XXX WHEN CONFIG* WILL BE IN PROPAGATED DRIVER_STATE XXX
   * ALL THAT PART SHOULD BE MANAGED BY main_loop EXCEPTION HANDLER *)
  with e when is_toplevel_error ~test e ->
    let err_mess fmt =
      Fmt.pf fmt "@[<v 0>include %s failed:@;@[%a@]@]"
        (L.unloc i.th_name)
        (pp_toplevel_error ~test incl_state) e
    in
    (* XXX will only reset params and options that are globals *)
    (* main_loop will return previous state anyway *)
    let _ : HistoryTP.state =
      HistoryTP.reset_from_state state.toplvl_state
    in
    Command.cmd_error (IncludeFailed err_mess)

(** The main loop body: do one command *)
and do_command
    ~(test : bool)
    (state : driver_state)
    (command : ProverLib.input) : driver_state
  =
  match ToplevelProver.get_mode state.toplvl_state, command with
                          (* ↓ touch toplvl_state and history_state ↓ *)
    | _, Toplvl Undo nb_undo            -> do_undo state nb_undo
                                       (* ↓ touch only toplvl_state ↓ *)
    | GoalMode, Prover InputDescr decls -> do_decls state decls
                                       (* ↓ touch only toplvl_state ↓ *)
    | _,        Prover Tactic l         -> do_tactic state l
                                            (* ↓ do not touch state ↓ *)
    | _,        Prover Print q          -> do_print state q
                                            (* ↓ do not touch state ↓ *)
    | _,        Prover Search t         -> do_search state t
                                       (* ↓ touch only toplvl_state ↓ *)
    | WaitQed,  Prover Qed              -> do_qed state
                                   (* ↓ touch only the table in p_s ↓ *)
    | GoalMode, Prover Hint h           -> do_add_hint state h
                        (* ↓ touch only Config params that are refs ↓ *)
    | GoalMode, Prover SetOption sp     -> do_set_option state sp
                                       (* ↓ touch only toplvl_state ↓ *)
    | GoalMode, Prover Goal g           -> do_add_goal state g
                                       (* ↓ touch only toplvl_state ↓ *)
    | GoalMode, Prover Proof            -> do_start_proof state
                              (* ↓ seems to touch only toplvl_state ↓ *)
    | GoalMode, Toplvl Include inc      -> do_include ~test state inc
                                  (* ↓ touch only toplvl_state mode ↓ *)
    | GoalMode, Prover EOF              -> do_eof state

    | WaitQed, Prover Abort ->
      if test then
        raise (Failure "Trying to abort a completed proof.");
      Command.cmd_error AbortIncompleteProof

                                      (* ↓ touch only toplvl_state ↓ *)
    | ProofMode, Prover Abort ->
      Printer.prt `Result
        "Exiting proof mode and aborting current proof.@.";
      { state with toplvl_state = 
          ToplevelProver.abort state.toplvl_state }

    | _, Prover Qed ->
      if test then raise Unfinished;
      Command.cmd_error Unexpected_command

    | _, _ -> Command.cmd_error Unexpected_command

(* FIXME why not using do_all_commands when not interactive ? *)
(** Do all command from a file until EOF is reached *)
and do_all_commands ~(test : bool) (state : driver_state) : driver_state =
  match next_input ~test state with
  | ProverLib.Prover EOF -> state
  | cmd -> do_all_commands ~test (do_command ~test state cmd)


(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
let rec main_loop ~test ?(save=true) (state : driver_state) =
  if !interactive then Printer.prt `Prompt "";

  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  let state = begin
    if save then
      {state with
       history_state =
        (* XXX ↓ impure ↓ XXX *)
         HistoryTP.save_state state.history_state
         state.toplvl_state
      }
    else state
  end in

  match
    let cmd = next_input ~test state in
    let new_state = do_command ~test state cmd
    in
    Server.update new_state.toplvl_state.prover_state;
    new_state, ToplevelProver.get_mode new_state.toplvl_state
  with
  (* exit prover *)
  | _, AllDone -> Printer.pr "Goodbye!@." ;
    (if !stat_filename <> "" then
      ProverTactics.pp_list_count !stat_filename);
    if not test && not !html then exit 0;

  (* loop *)
  | new_state, _ ->
    if !html then
      Html.pp ();
    (main_loop[@tailrec]) ~test new_state

  (* error handling *)
  | exception e when is_toplevel_error ~test e ->
    Printer.prt `Error "%a" (pp_toplevel_error ~test state) e;
    main_loop_error ~test state

and main_loop_error ~test (state : driver_state) : unit =
  if !interactive
  then begin (* at top-level, query again *)
    assert (state.file.f_path = `Stdin);
    (main_loop[@tailrec]) ~test ~save:false state
  end
  else if !html then 
    Fmt.epr "Error in file %s.sp:\nOutput stopped at previous call.\n" 
      state.file.f_name
  else if not test then exit 1

let start_main_loop
    ?(test=false)
    ~(main_mode : [`Stdin | `File of string])
    () : unit
  =
  (* interactive is only set here *)
  interactive := main_mode = `Stdin;
  let file = match main_mode with
    | `Stdin -> file_from_stdin ()
    | `File fname -> locate [LP_none] fname
  in

  (* XXX the state is mainly composed by attributes only "config"
   * and "option_defs" values do not change in the program *)
  let state = {
    (* XXX ↓ impure ↓ XXX Configs and option_defs are reset here *)
    toplvl_state = ToplevelProver.init ();

    history_state = HistoryTP.init_history_state;

    (* The check_mode can be changed regarding to includes main.ml:426 *)
    check_mode = `Check;

    (* load_paths set here once for all … *)
    load_paths = mk_load_paths ~main_mode ();

    (* current file can be changed regarding to includes main.ml:426 *)
    file;

    (* file_stack can be changed regarding to includes main.ml:426 *)
    file_stack = []; }
  in
  main_loop ~test state

let generate_html (filename : string) (html_filename : string) =
  Printer.init Printer.Html;
  if Filename.extension filename <> ".sp" then
    Command.cmd_error (InvalidExtention filename);
  Html.init filename html_filename;
  let name = Filename.chop_extension filename in
  html := true;
  start_main_loop ~test:false ~main_mode:(`File name) ();
  Html.close html_filename

let interactive_prover () =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.init Printer.Interactive;
  Server.start ();
  html := false;
  try start_main_loop ~main_mode:`Stdin ()
  with End_of_file -> Printer.prt `Error "End of file, exiting."

let run ?(test=false) (filename : string) : unit =
  if test then begin
    Printer.init Printer.Test;
    Format.eprintf "Running %S...@." filename
  end
  else
    Printer.init Printer.File;

  if Filename.extension filename <> ".sp" then
    Command.cmd_error (InvalidExtention filename);

  if (!stat_filename <> "") && 
     (Filename.extension !stat_filename <> ".json") then
    Command.cmd_error (InvalidExtention !stat_filename);

  let name = Filename.chop_extension filename in

  html := false;
  start_main_loop ~test ~main_mode:(`File name) ()

(* parse command line and check values before `run`ning *)
let main () =
  let args = ref [] in
  let html_filename = ref "" in
  let stat_filename = ref "" in
  let speclist = [
    ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
    ("--html", Arg.Set_string html_filename, "<file.html> Output a html file; Incompatible with -i");
    ("-v", Arg.Set verbose, "display more informations");
    ("--stat", Arg.Set_string stat_filename, "<stat.json> Output a json file
    with statistics (tactic count)");
  ] in

  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  html := !html_filename <> "";
  if !interactive && !html then
    Arg.usage speclist usage
  else if List.length !args = 0 && not !interactive then
    Arg.usage speclist usage
  else if List.length !args > 0 && !interactive then
    Printer.pr "No file arguments accepted when running in interactive mode.@."
  else if !interactive then
    interactive_prover ()
  else if !html then
    let filename = List.hd !args in
    generate_html filename !html_filename
  else
    let filename = List.hd !args in
    run filename
