open Utils

module L = Location

module Initialization = struct
  (* Opening these modules is only useful for their side effects,
   * e.g. registering tactics - hence the use of "open!" *)
  open! LowTactics
  open! TraceTactics
  open! EquivTactics
  open! HighTactics
end

(*--TOMOVE in Config ?-------- Command flags ------------------*)(* {↓{ *)
let interactive = ref false
let verbose = ref false
let html = ref false
let stat_filename = ref ""
(* }↑} *)

let usage = Fmt.str "Usage: %s filename" (Filename.basename Sys.argv.(0))

(*------------------------------------------------------------------*)
(** A loading path: directory to lookup during includes *)
type load_path =
  | LP_dir of string
  | LP_none

type load_paths = load_path list

type file = {
  f_name   : string;                     (** short name, no extention *)
  f_path   : [`Stdin | `File of string]; (** file path *)
  f_lexbuf : Lexing.lexbuf;
}

module ToplevelProver = TopLevel.Toplevel(Prover)
module HistoryTP = History.HistoryTopLevelProver(ToplevelProver)

(** State of the main loop. *)
type driver_state = {
  toplvl_state : ToplevelProver.state;
  (* toplvl_state : ToplevelProver.state = {
      prover_state : Prover.state = {
        goals        : Proverlib.pending_proof list;
        table        : Symbols.table; 
        current_goal : Proverlib.pending_proof option;
        subgoals     : Goal.t list;
        bullets      : Bullets.path;
      }
      params       : Config.params; (* save global params… *)
      option_defs  : Proverlib.option_def list; (* save global option_def *)
      prover_mode  : Proverlib.prover_mode;
    }
  *)

  (* ↓ history of toplvl_state ↑ *)
  history_state : HistoryTP.history_state;

  (* The check_mode can be changed regarding to includes main.ml:426 *)
  check_mode : [`Check | `NoCheck];

  (* load_paths set once for all in start_main_loop *)
  load_paths : load_paths;
  (** load paths *)

  (* current file can be changed regarding to do_include *)
  file : file;
  (** current file *)

  (* file_stack can be changed regarding to do_include *)
  file_stack : file list;
  (** stack of nested opened files *)
}

(*--------------- Driver -------------------------------------------*)
let get_lexbuf (state : driver_state) : string * Lexing.lexbuf = 
  let lexbuf = match state.file.f_path with
    | `Stdin -> Lexing.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere). *)

    | `File _ -> state.file.f_lexbuf
  in
  state.file.f_name ^ ".sp", lexbuf

(*---------------- Driver ------------------------------------------*)
(** Print precise location error (to be caught by emacs) *)
let pp_loc_error (state:driver_state) ppf loc =
  if !interactive then
    match state.file.f_path with
    | `Stdin ->
      let lexbuf = Lexing.from_channel stdin in
      let startpos = lexbuf.Lexing.lex_curr_p.pos_cnum in
      Fmt.pf ppf
        "[error-%d-%d]@;"
        (max 0 (loc.L.loc_bchar - startpos))
        (max 0 (loc.L.loc_echar - startpos))
    | `File f ->
      let loc = { loc with L.loc_fname = f; } in
      Fmt.pf ppf "%s:@;" (L.tostring loc)


let pp_loc_error_opt (state:driver_state) ppf = function
  | None -> ()
  | Some l -> pp_loc_error state ppf l


(*--------------- Driver -------------------------------------------*)
let check_cycle (state : driver_state) (name : string) : unit =
  let has_cycle =
    List.exists (fun file -> file.f_name = name) state.file_stack
  in
  if has_cycle then Command.cmd_error (IncludeCycle name)

(*--------------- Driver -------------------------------------------*)
let file_from_stdin () : file =
  { f_name = "#stdin";
    f_path = `Stdin;
    f_lexbuf = Lexing.from_channel stdin; }
    
(*--------------- Driver -------------------------------------------*)
let file_from_path (dir : load_path) (partial_path : string) : file option =
  let partial_path_ext = partial_path ^ ".sp" in
  try
    let path = match dir with
      | LP_none    -> partial_path_ext
      | LP_dir dir -> Filename.concat dir partial_path_ext
    in

    let chan = Stdlib.open_in path in
    let lexbuf = Lexing.from_channel chan in

    Some { f_name   = partial_path;
           f_path   = `File path;
           f_lexbuf = lexbuf; }
  with
  | Sys_error _ -> None

(*------ TOMOVE in Utils or Commandline ? --------------------------*)
let valid_theory_regexp = Pcre.regexp "[a-zA-Z][[a-zA-Z0-9]*"

(** try to locate a file according to some loading paths *) 
let locate (lds : load_paths) (name : string) : file =
  if not (Pcre.pmatch ~rex:valid_theory_regexp name) then
    Command.cmd_error (InvalidTheoryName name);  (* FIXME: location *)  

  let rec try_dirs (dirs : load_paths) : file =
    match dirs with
    | [] -> Command.cmd_error (IncludeNotFound name)
    | dir :: dirs ->
       match file_from_path dir name with
       | Some file -> file
       | None -> try_dirs dirs
  in
  try_dirs lds

(*--------------- Driver -------------------------------------------*)
let include_get_file (state : driver_state) (name : Theory.lsymb) : file =
  check_cycle state (L.unloc name);

  locate state.load_paths (L.unloc name)

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

(** check if an exception is handled *)
let is_toplevel_error ~test (e : exn) : bool =
  match e with
  | Parserbuf.Error                 _
  | Proverlib.Error                 _
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

  | Proverlib.Error e ->
    Proverlib.pp_error pp_loc_error fmt e

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

(** Get the next input from the current file. Driver *)
let next_input ~test (state : driver_state) :
Proverlib.parsed_input =
  let filename, lexbuf = get_lexbuf state in
  Parserbuf.parse_from_buf
    ~test ~interactive:!interactive
    (if state.toplvl_state.prover_mode = Proverlib.ProofMode then
       Parser.top_proofmode
     else
       Parser.interactive)
    lexbuf ~filename

(*---------------- Main --------------------------------------------*)
let do_undo (state : driver_state) (nb_undo : int) : driver_state =
  let history_state, toplvl_state =
  HistoryTP.reset_state state.history_state nb_undo in
  let () = match toplvl_state.prover_mode with
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

let do_print (state : driver_state) (q : Proverlib.print_query) 
  : driver_state =
  ToplevelProver.do_print state.toplvl_state q;
  state

(*---------type of parsed element for tactics, braces and bullets---*)
type parsed_t = [`Brace of [`Close | `Open]
      | `Bullet of string
      | `Tactic of TacticsArgs.parser_arg Tactics.ast]
(*----------Part can be done here and tactic handling in Prover ----*)
let do_tactic (state : driver_state) (l:parsed_t list) : driver_state =
  begin match state.check_mode with
    | `NoCheck -> assert (state.toplvl_state.prover_mode = WaitQed)
    | `Check   -> 
      if state.toplvl_state.prover_mode <> Proverlib.ProofMode then
        Command.cmd_error Unexpected_command;
  end;

  if not !interactive then 
  begin
    let lnum = state.file.f_lexbuf.lex_curr_p.pos_lnum in
    match List.filter_map 
            (function `Tactic t -> Some t | _ -> None) l with
      | [utac] ->
          Printer.prt `Prompt "Line %d: %a" lnum ProverTactics.pp_ast utac
      | _ ->
          Printer.prt `Prompt "Line %d: ??" lnum
  end;

  match state.check_mode with
  | `NoCheck -> state
  | `Check   ->
    let saved_ps = ToplevelProver.copy state.toplvl_state in
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

(*----------------- Driver -----------------------------------------*)
  (* XXX Touch global Config that has to be recorded in History *)
let do_set_option (state : driver_state) (sp : Config.p_set_param) :
  driver_state =
  match Config.set_param sp with
  | `Failed s -> Command.cmd_error (InvalidSetOption s)
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
    (i : Proverlib.include_param) 
  : driver_state 
  =
  (* save prover state, in case the include fails *)
  (* FIXME Just take back state.toplvl_state of given original state ? *)
  let toplvl_state = ToplevelProver.copy state.toplvl_state in

  let file = include_get_file state i.th_name in
  let file_stack = state.file :: state.file_stack in

  let hstate = { state with 
     history_state = HistoryTP.push_pt_history state.history_state }
  in

  (* XXX ? check_mode can change value here regarding to params !*)
  let check_mode = 
    if List.exists (fun x -> L.unloc x = "admit") i.Proverlib.params 
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
    let _ : HistoryTP.state =
      HistoryTP.reset_from_state toplvl_state
    in
    Command.cmd_error (IncludeFailed err_mess)

(** The main loop body: do one command *)
and do_command
    ~(test : bool)
    (state : driver_state)
    (command : Proverlib.parsed_input) : driver_state
  =
  match state.toplvl_state.prover_mode, command with
                          (* ↓ touch toplvl_state and history_state ↓ *)
    | _, ParsedUndo nb_undo            -> do_undo state nb_undo
                                       (* ↓ touch only toplvl_state ↓ *)
    | GoalMode, ParsedInputDescr decls -> do_decls state decls
                                       (* ↓ touch only toplvl_state ↓ *)
    | _,        ParsedTactic l         -> do_tactic state l
                                            (* ↓ do not touch state ↓ *)
    | _,        ParsedPrint q          -> do_print state q
                                       (* ↓ touch only toplvl_state ↓ *)
    | WaitQed,  ParsedQed              -> do_qed state
                                   (* ↓ touch only the table in p_s ↓ *)
    | GoalMode, ParsedHint h           -> do_add_hint state h
                        (* ↓ touch only Config params that are refs ↓ *)
    | GoalMode, ParsedSetOption sp     -> do_set_option state sp
                                       (* ↓ touch only toplvl_state ↓ *)
    | GoalMode, ParsedGoal g           -> do_add_goal state g
                                       (* ↓ touch only toplvl_state ↓ *)
    | GoalMode, ParsedProof            -> do_start_proof state
                        (* ↓ FIXME seems to touch only toplvl_state ↓ *)
    | GoalMode, ParsedInclude inc      -> do_include ~test state inc
                                  (* ↓ touch only toplvl_state mode ↓ *)
    | GoalMode, EOF                    -> do_eof state

    | WaitQed, ParsedAbort ->
      if test then
        raise (Failure "Trying to abort a completed proof.");
      Command.cmd_error AbortIncompleteProof

                                      (* ↓ touch only toplvl_state ↓ *)
    | ProofMode, ParsedAbort ->
      Printer.prt `Result
        "Exiting proof mode and aborting current proof.@.";
      { state with toplvl_state = 
          ToplevelProver.abort state.toplvl_state }

    | _, ParsedQed ->
      if test then raise Unfinished;
      Command.cmd_error Unexpected_command

    | _, _ -> Command.cmd_error Unexpected_command

(* FIXME why not using do_all_commands when not interactive ? *)
(** Do all command from a file until EOF is reached *)
and do_all_commands ~(test : bool) (state : driver_state) : driver_state =
  match next_input ~test state with
  | EOF -> state
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
    Server.update ();
    new_state, new_state.toplvl_state.prover_mode
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
    (* FIXME original state with new history ? *)
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

let mk_load_paths ~main_mode () : load_paths =
  let exec_dir = Filename.dirname Sys.executable_name in
  (* let exec_dir = Filename.dirname (Sys.argv.(0)) in *)
  let theory_dir =
    Filename.(concat exec_dir "theories")
  in
  let theory_load_path = LP_dir theory_dir in
  let top_load_path =
    match main_mode with
    | `Stdin     -> LP_dir (Sys.getcwd ())
    | `File path -> LP_dir (Filename.dirname path)
  in
  [top_load_path; theory_load_path]

(* `test arg should be global ? FIXME *)
let start_main_loop
    ?(test=false)
    ~(main_mode : [`Stdin | `File of string])
    () : unit
  =
  (* FIXME interactive is only set here *)
  interactive := main_mode = `Stdin;
  let file = match main_mode with
    | `Stdin -> file_from_stdin ()
    | `File fname -> locate [LP_none] fname
  in

  (* FIXME the state is mainly composed by attributes only "config" 
   * values that do not change in the program : that is global
   * immutable values (possibly ref in Config) *)
  let state = {
    (* XXX ↓ impure ↓ XXX Configs are reset here *)
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

(*------------------- Tests -----------------------------------*)(* {↓{ *)
let () =
  let exception Ok in
  let test = true in
  Checks.add_suite "Tactics" [
    "Exists Intro", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/existsintro_fail.sp" with
           | Symbols.(Error (_, Unbound_identifier "a1")) -> raise Ok)
    end ;
    "TS not leq", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/ts_leq_not_lt.sp" with
           | Unfinished -> raise Ok)
    end ;
(* TODO: rework these tests.
   They were checking that the tactics failed as expected in cases
   where they were not supposed to apply. However, these tactics have been 
   generalised and now actually apply in these cases. *)
(*    "SEnc Bad SSC - INTCTXT 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_nornd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;
    "SEnc Bad SSC - INTCTXT 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_rndnotfresh.sp" with
           | Tactics.Tactic_soft_failure (_,SEncRandomNotFresh) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_sharedrnd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 4", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_sharedrndind.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;*)
   (* "Senc Bad SSC - CCA 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_sharedrnd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_sharedrndframe.sp" with
           | Tactics.Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_nornd.sp" with
           | Tactics.Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;*)
    "Axiom Systems - 0", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/axiom2.sp" with
           | Tactics.Tactic_soft_failure (_,NoAssumpSystem _) -> raise Ok)
    end ;
    "Axiom Systems - 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/axiom3.sp" with
           | Symbols.Error (_, Symbols.Unbound_identifier "test") ->
             raise Ok)
    end ;
    "Substitution no capture", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/capture.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Not Depends", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/depends.sp" with
           | Tactics.Tactic_soft_failure (_, Tactics.NotDepends _)
             -> raise Ok)
    end ;
    "Fresh Not Ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_reach_var.sp" with
           | Tactics.Tactic_soft_failure
               (_, Tactics.Failure "can only be applied on ground terms") ->
             raise Ok)
    end ;
    "Check equalities false if unsupported terms", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/completion_unsupported_term.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Indexed abstract", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/idx_abs.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.GoalNotClosed) -> raise Ok)
    end ;
    "Find equality", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/try.sp" with
           | Tactics.Tactic_soft_failure (_,CongrFail) -> raise Ok)
    end ;
    "Undo does not maintain old truth", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/undo.sp" with
           | Unfinished -> raise Ok)
    end ;
  ] ;

  (*------------------------------------------------------------------*)
  Checks.add_suite "Equivalence" [
    "Fresh Frame", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_frame.sp" with
           | Unfinished -> raise Ok)
    end ;
    "Fresh System", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_system.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.GoalNotClosed) ->
             raise Ok)
    end ;
    "DDH", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/ddh.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.NotDDHContext) -> raise Ok)
    end ;

    "FA Dup Input", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fadup_input.sp" with
           | Tactics.Tactic_soft_failure (_,Tactics.NoReflMacroVar) -> raise Ok)
    end ;
    "XOR2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/xor2.sp" with
           | Tactics.Tactic_soft_failure
               (_, Failure "name is not XORed on both sides") ->
             raise Ok)
    end ;
    "Not XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/notxor.sp" with
           | Tactics.Tactic_soft_failure
               (_, Failure "Xor can only be applied on a term with at least one \
                            occurrence of a term xor(t,k)")  ->
             raise Ok)
    end ;
    "Pred Init", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/pred.sp" with
           | Unfinished -> raise Ok)
    end ;
    "DDH not PQ Sound", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/pqsound.sp" with
           | Tactics.Tactic_hard_failure (_,Tactics.TacticNotPQSound) -> raise Ok)
    end
  ];

  (*------------------------------------------------------------------*)
  Checks.add_suite "Include" [
    "Cycle", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/IncludeCycle.sp" with
           | Command.Cmd_error (IncludeCycle _) -> raise Ok)
    end ;
    "Theory not found", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-unknown.sp" with
           | Command.Cmd_error (IncludeNotFound _) -> raise Ok)
    end ;
    (* Not that in test mode, errors during an include are not wrapped
       into a IncludeError.  *)
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind.sp" with
           | Symbols.(Error (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind2.sp" with
           | Symbols.(Error (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Undefined Action", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/bad-actions.sp" with
             Theory.Conv (_, UndefInSystem _) -> raise Ok)
    end ;
  ]
(* }↑} *)
