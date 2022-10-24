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

(** State of the main loop. *)
(* TODO: include everything currently handled statefully in Prover.ml *)
type main_state = {
  mode  : Prover.prover_mode;
  table : Symbols.table;

  check_mode : [`Check | `NoCheck];

  interactive : bool;
  html : bool;

  load_paths : load_paths;
  (** load paths *)

  file : file;
  (** current file *)

  file_stack : file list;
  (** stack of nested opened files *)
}

(*------------------------------------------------------------------*)
let get_lexbuf (state : main_state) : string * Lexing.lexbuf = 
  let lexbuf = match state.file.f_path with
    | `Stdin -> Lexing.from_channel stdin
    (* we need to re-compute the lexer buffer from the input channel, or error
       messages are not acurate afterward. I do not understand why exactly (the
       lexer buffer positions must not be properly updated somewhere). *)

    | `File _ -> state.file.f_lexbuf
  in
  state.file.f_name ^ ".sp", lexbuf

(*------------------------------------------------------------------*)
(** Print precise location error (to be caught by emacs) *)
let pp_loc_error state ppf loc =
  if state.interactive then
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


let pp_loc_error_opt state ppf = function
  | None -> ()
  | Some l -> pp_loc_error state ppf l

type cmd_error =
  | Unexpected_command
  | AbortIncompleteProof
  | InvalidExtention  of string
  | StartProofError   of string
  | InvalidTheoryName of string
  | IncludeCycle      of string
  | IncludeNotFound   of string
  | IncludeFailed     of (Format.formatter -> unit)
  | InvalidSetOption  of string

exception Cmd_error of cmd_error

let pp_cmd_error fmt = function
  | Unexpected_command   -> Fmt.pf fmt "Unexpected command."

  | StartProofError s    -> Fmt.pf fmt "%s" s

  | AbortIncompleteProof -> Fmt.pf fmt "Trying to abort a completed proof."

  | InvalidTheoryName s  -> Fmt.pf fmt "invalid theory name %s" s

  | IncludeCycle s       -> Fmt.pf fmt "include cycle (%s)" s

  | IncludeNotFound s    -> Fmt.pf fmt "could not locate theory: %s" s

  | InvalidExtention s   -> Fmt.pf fmt "invalid extention (not a .sp): %s" s

  | IncludeFailed err    -> Fmt.pf fmt "%t" err

  | InvalidSetOption s   -> Fmt.pf fmt "set failed: %s" s

let cmd_error e = raise (Cmd_error e)


(*------------------------------------------------------------------*)
let valid_theory_regexp = Pcre.regexp "[a-zA-Z][[a-zA-Z0-9]*"

let check_cycle (state : main_state) (name : string) : unit =
  let has_cycle =
    List.exists (fun file -> file.f_name = name) state.file_stack
  in
  if has_cycle then cmd_error (IncludeCycle name)

let file_from_stdin () : file =
  { f_name = "#stdin";
    f_path = `Stdin;
    f_lexbuf = Lexing.from_channel stdin; }
    

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

(** try to locate a file according to some loading paths *) 
let locate (lds : load_paths) (name : string) : file =
  if not (Pcre.pmatch ~rex:valid_theory_regexp name) then
    cmd_error (InvalidTheoryName name);  (* FIXME: location *)  

  let rec try_dirs (dirs : load_paths) : file =
    match dirs with
    | [] -> cmd_error (IncludeNotFound name)
    | dir :: dirs ->
       match file_from_path dir name with
       | Some file -> file
       | None -> try_dirs dirs
  in
  try_dirs lds


let include_get_file (state : main_state) (name : Theory.lsymb) : file =
  check_cycle state (L.unloc name);

  locate state.load_paths (L.unloc name)

(*------------------------------------------------------------------*)
(** {2 Error handling} *)

open Tactics

(** check if an exception is handled *)
let is_toplevel_error ~test interactive (e : exn) : bool =
  match e with
  | Parserbuf.Error         _
  | Prover.Error       _
  | Cmd_error               _
  | Process.ProcError       _
  | ProcessDecl.Decl_error  _
  | Theory.Conv             _
  | Symbols.SymbError       _
  | System.Error            _
  | SystemExpr.Error        _
  | Tactic_soft_failure     _
  | Tactic_hard_failure     _ -> not test

  | _e when interactive -> not test

  | _ -> false

(** [is_toplevel_error] must be synchronized with [pp_toplevel_error] *)
let pp_toplevel_error
    ~test
    (state : main_state)
    (fmt : Format.formatter)
    (e : exn) : unit
  =
  let pp_loc_error     = pp_loc_error     state in
  let pp_loc_error_opt = pp_loc_error_opt state in

  match e with
  | Parserbuf.Error s ->
    Fmt.string fmt s

  | Prover.Error e ->
    Prover.pp_error pp_loc_error fmt e

  | Cmd_error e ->
    pp_cmd_error fmt e

  | Process.ProcError e ->
    (Process.pp_proc_error pp_loc_error) fmt e

  | ProcessDecl.Decl_error e when not test ->
    (ProcessDecl.pp_decl_error pp_loc_error) fmt e

  | Theory.Conv e when not test ->
    (Theory.pp_error pp_loc_error) fmt e

  | Symbols.SymbError e when not test ->
    (Symbols.pp_symb_error pp_loc_error) fmt e

  | System.Error e when not test ->
    Format.fprintf fmt "System error: %a" System.pp_error e

  | SystemExpr.Error e when not test ->
    Format.fprintf fmt "System error: %a" SystemExpr.pp_error e

  | Tactic_soft_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic failed: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | Tactic_hard_failure (l,e) when not test ->
    Fmt.pf fmt "%aTactic ill-formed or unapplicable: %a"
      pp_loc_error_opt l
      Tactics.pp_tac_error_i e

  | e when state.interactive ->
    Fmt.pf fmt "Anomaly, please report: %s" (Printexc.to_string e)
    
  | _ -> assert false

(*------------------------------------------------------------------*)

exception Unfinished

(** Get the next input from the current file. *)
let next_input ~test (state : main_state) : Prover.parsed_input =
  let filename, lexbuf = get_lexbuf state in
  Parserbuf.parse_from_buf
    ~test ~interactive:state.interactive
    (if state.mode = Prover.ProofMode then
       Parser.top_proofmode
     else
       Parser.interactive)
    lexbuf ~filename

(*------------------------------------------------------------------*)
let do_undo (state : main_state) (nb_undo : int) : main_state =
  let new_mode, new_table = Prover.reset_state nb_undo in
  let () = match new_mode with
    | ProofMode -> Printer.pr "%a" Prover.pp_goal ()
    | GoalMode -> Printer.pr "%a" Action.pp_actions new_table
    | WaitQed -> ()
    | AllDone -> assert false in
  { state with mode = new_mode; table = new_table; }

(*------------------------------------------------------------------*)
let do_decls (state : main_state) (decls : Decl.declarations) : main_state =
  let table, proof_obls = ProcessDecl.declare_list state.table decls in

  if proof_obls <> [] then
    Printer.pr "@[<v 2>proof obligations:@;%a@]"
      (Fmt.list ~sep:Fmt.cut Goal.pp_init) proof_obls;

  List.iter Prover.add_proof_obl proof_obls;

  { state with mode = GoalMode; table = table; }

(*------------------------------------------------------------------*)
let do_print (state : main_state) (q : Prover.print_query) : main_state =
  match q with
  | Prover.Pr_statement l -> 
    let lem = Lemma.find l state.table in
    Printer.prt `Default "%a" Lemma.pp lem;
    state

  | Prover.Pr_system s_opt ->
    let system = 
      match s_opt with
      | None   -> 
        begin match Prover.get_current_system () with
          | Some s -> s.set
          | None -> hard_failure (Failure "no default system");
        end

      | Some s -> SystemExpr.parse state.table s
    in
    SystemExpr.print_system state.table system;

    if Config.print_trs_equations ()
    then
      Printer.prt `Result "@[<v>@;%a@;@]%!"
        Completion.print_init_trs state.table;

    state

(*------------------------------------------------------------------*)
let do_tactic (state : main_state) l : main_state =
  begin match state.check_mode with
    | `NoCheck -> assert (state.mode = WaitQed)
    | `Check   -> 
      if state.mode <> Prover.ProofMode then
        cmd_error Unexpected_command;
  end;

  if not state.interactive then begin
    let lnum = state.file.f_lexbuf.lex_curr_p.pos_lnum in
    match List.filter_map (function `Tactic t -> Some t | _ -> None) l with
      | [utac] ->
          Printer.prt `Prompt "Line %d: %a" lnum Prover.pp_ast utac
      | _ ->
          Printer.prt `Prompt "Line %d: ??" lnum
  end;

  match state.check_mode with
  | `NoCheck -> state
  | `Check   ->
    let prover_state = Prover.get_state state.mode state.table in
    begin try
      List.iter
        (function
           | `Bullet bl    -> Prover.open_bullet bl 
           | `Brace `Open  -> Prover.open_brace ()
           | `Brace `Close -> Prover.close_brace ()
           | `Tactic utac  -> Prover.eval_tactic utac)
        l
    with
      | e -> 
        ignore (Prover.reset_from_state prover_state) ; raise e
    end ;
    if Prover.is_proof_completed () then begin
      Printer.prt `Goal "Goal %s is proved"
        (Utils.oget (Prover.current_goal_name ()));
      { state with mode = WaitQed }
    end else begin
      Printer.pr "%a" Prover.pp_goal ();
      { state with mode = ProofMode }
    end

(*------------------------------------------------------------------*)
let do_qed (state : main_state) : main_state =
  let table = Prover.complete_proof state.table in
  Printer.prt `Result "Exiting proof mode.@.";
  { state with table; mode = GoalMode }

(*------------------------------------------------------------------*)
let do_add_hint (state : main_state) (h : Hint.p_hint) : main_state =
  let module PD = ProcessDecl in
  let table =
    match h with
    | Hint.Hint_rewrite id -> PD.add_hint_rewrite state.table id state.table
    | Hint.Hint_smt     id -> PD.add_hint_smt     state.table id state.table
  in
  { state with table; }

(*------------------------------------------------------------------*)
let do_set_option (state : main_state) (sp : Config.p_set_param) : main_state =
  match Config.set_param sp with
  | `Failed s -> cmd_error (InvalidSetOption s)
  | `Success -> state

(*------------------------------------------------------------------*)
let do_add_goal 
    (state : main_state)
    (g : Goal.Parsed.t Location.located) 
  : main_state 
  =
  let i,f = Prover.add_new_goal state.table g in
  Printer.pr "@[<v 2>Goal %s :@;@[%a@]@]@." i Goal.pp_init f;
  state

(*------------------------------------------------------------------*)
let do_start_proof (state : main_state) : main_state =
  match Prover.start_proof state.check_mode with
  | None ->
    Printer.pr "%a" Prover.pp_goal ();
    let mode = match state.check_mode with
      | `NoCheck -> Prover.WaitQed 
      | `Check   -> Prover.ProofMode
    in
    { state with mode }
  | Some es -> cmd_error (StartProofError es)

(*------------------------------------------------------------------*)
let do_eof (state : main_state) : main_state =
  assert (state.file_stack = []);
  { state with mode = AllDone; }

(*------------------------------------------------------------------*)
let rec do_include 
    ~test
    (state : main_state)
    (i : Prover.include_param) 
  : main_state 
  =
  (* save prover state, in case the include fails *)
  let prover_state = Prover.get_state state.mode state.table in

  let file = include_get_file state i.th_name in
  let file_stack = state.file :: state.file_stack in

  Prover.push_pt_history ();

  let check_mode = 
    if List.exists (fun x -> L.unloc x = "admit") i.Prover.params 
    then `NoCheck
    else `Check
  in
  let incl_state = { state with file; file_stack; check_mode; } in

  (* try to do the include *)
  try
    let final_state = do_all_commands ~test incl_state in
    Printer.prt `Warning "loaded: %s.sp@;" final_state.file.f_name;

    Prover.pop_pt_history ();

    { final_state with file       = state.file; 
                       file_stack = state.file_stack; 
                       check_mode = state.check_mode; }

  (* include failed, revert state *)
  with e when is_toplevel_error ~test state.interactive e ->
    let err_mess fmt =
      Fmt.pf fmt "@[<v 0>include %s failed:@;@[%a@]@]"
        (L.unloc i.th_name)
        (pp_toplevel_error ~test incl_state) e
    in
    Prover.pop_pt_history ();
    let _ : Prover.prover_mode * Symbols.table =
      Prover.reset_from_state prover_state
    in
    cmd_error (IncludeFailed err_mess)

(** The main loop body: do one command *)
and do_command
    ~(test : bool)
    (state : main_state)
    (command : Prover.parsed_input) : main_state
  =
  match state.mode, command with
    | _, ParsedUndo nb_undo            -> do_undo state nb_undo

    | GoalMode, ParsedInputDescr decls -> do_decls state decls

    | _,        ParsedTactic l         -> do_tactic state l

    | _,        ParsedPrint q          -> do_print state q

    | WaitQed,  ParsedQed              -> do_qed state

    | GoalMode, ParsedHint h           -> do_add_hint state h

    | GoalMode, ParsedSetOption sp     -> do_set_option state sp

    | GoalMode, ParsedGoal g           -> do_add_goal state g

    | GoalMode, ParsedProof            -> do_start_proof state

    | GoalMode, ParsedInclude inc      -> do_include ~test state inc

    | GoalMode, EOF                    -> do_eof state

    | WaitQed, ParsedAbort ->
      if test then
        raise (Failure "Trying to abort a completed proof.");

      cmd_error AbortIncompleteProof

    | ProofMode, ParsedAbort ->
      Printer.prt `Result "Exiting proof mode and aborting current proof.@.";
      Prover.abort ();
      { state with mode = GoalMode; }

    | _, ParsedQed ->
      if test then raise Unfinished;
      
      cmd_error Unexpected_command

    | _, _ -> cmd_error Unexpected_command

(** Do all command from a file until EOF is reached *)
and do_all_commands ~(test : bool) (state : main_state) : main_state =
  match next_input ~test state with
  | EOF -> state
  | cmd -> do_all_commands ~test (do_command ~test state cmd)


(** The main loop of the prover. The mode defines in what state the prover is,
    e.g is it waiting for a proof script, or a system description, etc.
    [save] allows to specify is the current state must be saved, so that
    one can backtrack.
*)
let rec main_loop ~test ?(save=true) (state : main_state) =
  if state.interactive then Printer.prt `Prompt "";

  (* Save the state if instructed to do so.
   * In practice we save except after errors and the first call. *)
  if save then Prover.save_state state.mode state.table ;

  match
    let cmd = next_input ~test state in
    let new_state = do_command ~test state cmd
    in
    Server.update ();
    new_state, new_state.mode
  with
  (* exit prover *)
  | new_state, AllDone -> Printer.pr "Goodbye!@." ;
    if not test && not new_state.html then exit 0;

  (* loop *)
  | new_state, _ ->
    if new_state.html then
      Html.pp ();
    (main_loop[@tailrec]) ~test new_state

  (* error handling *)
  | exception e when is_toplevel_error ~test state.interactive e ->
    Printer.prt `Error "%a" (pp_toplevel_error ~test state) e;
    main_loop_error ~test state

and main_loop_error ~test (state : main_state) : unit =
  if state.interactive
  then begin (* at top-level, query again *)
    assert (state.file.f_path = `Stdin);
    (main_loop[@tailrec]) ~test ~save:false state
  end
  else if state.html then 
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

let start_main_loop
    ?(test=false)
    ?(html=false)
    ~(main_mode : [`Stdin | `File of string])
    () : unit
  =
  let interactive = main_mode = `Stdin in
  let file = match main_mode with
    | `Stdin -> file_from_stdin ()
    | `File fname -> locate [LP_none] fname
  in

  Prover.reset ();
  let state = {
    mode = GoalMode;
    table = Symbols.builtins_table;

    interactive;
    html;

    check_mode = `Check;

    load_paths = mk_load_paths ~main_mode ();

    file;

    file_stack = []; }
  in

  main_loop ~test state

let generate_html (filename : string) (html_filename : string) =
  Printer.init Printer.Html;
  if Filename.extension filename <> ".sp" then
    cmd_error (InvalidExtention filename);
  Html.init filename html_filename;
  let name = Filename.chop_extension filename in
  start_main_loop ~test:false ~html:true ~main_mode:(`File name) ();
  Html.close html_filename



let interactive_prover () =
  Printer.prt `Start "Squirrel Prover interactive mode.";
  Printer.prt `Start "Git commit: %s" Commit.hash_commit;
  Printer.init Printer.Interactive;
  Server.start ();
  try start_main_loop ~html:false ~main_mode:`Stdin ()
  with End_of_file -> Printer.prt `Error "End of file, exiting."

let run ?(test=false) (filename : string) : unit =
  if test then begin
    Printer.init Printer.Test;
    Format.eprintf "Running %S...@." filename
  end
  else
    Printer.init Printer.File;

  if Filename.extension filename <> ".sp" then
    cmd_error (InvalidExtention filename);

  let name = Filename.chop_extension filename in

  start_main_loop ~test ~html:false ~main_mode:(`File name) ()


let main () =
  let args = ref [] in
  let verbose = ref false in
  let interactive = ref false in
  let html_filename = ref "" in
  let speclist = [
    ("-i", Arg.Set interactive, "interactive mode (e.g, for proof general)");
    ("--html", Arg.Set_string html_filename, "<file.html> Output a html file; Incompatible with -i");
    ("-v", Arg.Set verbose, "display more informations");
  ] in

  let collect arg = args := !args @ [arg] in
  let _ = Arg.parse speclist collect usage in
  let html = !html_filename <> "" in
  if !interactive && html then
    Arg.usage speclist usage
  else if List.length !args = 0 && not !interactive then
    Arg.usage speclist usage
  else if List.length !args > 0 && !interactive then
    Printer.pr "No file arguments accepted when running in interactive mode.@."
  else if !interactive then
    interactive_prover ()
  else if html then
    let filename = List.hd !args in
    generate_html filename !html_filename
  else
    let filename = List.hd !args in
    run filename


(*------------------------------------------------------------------*)
let () =
  let exception Ok in
  let test = true in
  Checks.add_suite "Tactics" [
    "Exists Intro", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/existsintro_fail.sp" with
           | Symbols.(SymbError (_, Unbound_identifier "a1")) -> raise Ok)
    end ;
    "TS not leq", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/ts_leq_not_lt.sp" with
           | Unfinished -> raise Ok)
    end ;
(*    "SEnc Bad SSC - INTCTXT 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_nornd.sp" with
           | Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;
    "SEnc Bad SSC - INTCTXT 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_rndnotfresh.sp" with
           | Tactic_soft_failure (_,SEncRandomNotFresh) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_sharedrnd.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - INTCTXT 4", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/intctxt_sharedrndind.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;*)
    "Senc Bad SSC - CCA 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_sharedrnd.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_sharedrndframe.sp" with
           | Tactic_soft_failure (_,SEncSharedRandom) -> raise Ok)
    end ;
    "Senc Bad SSC - CCA 3", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/cca_nornd.sp" with
           | Tactic_soft_failure (_,SEncNoRandom) -> raise Ok)
    end ;
    "Axiom Systems - 0", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/axiom2.sp" with
           | Tactic_hard_failure (_,NoAssumpSystem) -> raise Ok)
    end ;
    "Axiom Systems - 1", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/axiom3.sp" with
           | Symbols.SymbError (_, Symbols.Unbound_identifier "test") ->
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
           | Tactic_soft_failure (_, Tactics.NotDepends _)
             -> raise Ok)
    end ;
    "Fresh Not Ground", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fresh_reach_var.sp" with
           | Tactic_soft_failure
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
           | Tactic_soft_failure (_,Tactics.GoalNotClosed) -> raise Ok)
    end ;
    "Find equality", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/try.sp" with
           | Tactic_soft_failure (_,CongrFail) -> raise Ok)
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
           | Tactic_soft_failure (_,Tactics.NotDDHContext) -> raise Ok)
    end ;

    "FA Dup Input", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/fadup_input.sp" with
           | Tactic_soft_failure (_,Tactics.NoReflMacroVar) -> raise Ok)
    end ;
    "XOR2", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/xor2.sp" with
           | Tactic_soft_failure
               (_, Failure "name is not XORed on both sides") ->
             raise Ok)
    end ;
    "Not XOR", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/notxor.sp" with
           | Tactic_soft_failure
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
           | Tactic_hard_failure (_,Tactics.TacticNotPQSound) -> raise Ok)
    end
  ];

  (*------------------------------------------------------------------*)
  Checks.add_suite "Include" [
    "Cycle", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/IncludeCycle.sp" with
           | Cmd_error (IncludeCycle _) -> raise Ok)
    end ;
    "Theory not found", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-unknown.sp" with
           | Cmd_error (IncludeNotFound _) -> raise Ok)
    end ;
    (* Not that in test mode, errors during an include are not wrapped
       into a IncludeError.  *)
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind.sp" with
           | Symbols.(SymbError (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Re-define", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/include-rebind2.sp" with
           | Symbols.(SymbError (_, Multiple_declarations _)) ->
             raise Ok)
    end ;
    "Undefined Action", `Quick, begin fun () ->
      Alcotest.check_raises "fails" Ok
        (fun () ->
           try run ~test "tests/alcotest/bad-actions.sp" with
             Theory.Conv (_, UndefInSystem _) -> raise Ok)
    end ;
  ]
